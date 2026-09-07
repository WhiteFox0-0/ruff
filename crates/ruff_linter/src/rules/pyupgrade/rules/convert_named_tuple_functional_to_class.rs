use log::debug;

use ruff_macros::{ViolationMetadata, derive_message_formats};
use ruff_python_ast::helpers::is_dunder;
use ruff_python_ast::name::Name;
use ruff_python_ast::{
    self as ast, Arguments, DecoratorList, Expr, ExprContext, Identifier, Keyword, Stmt, Suite,
};
use ruff_python_codegen::Generator;
use ruff_python_semantic::SemanticModel;
use ruff_python_stdlib::identifiers::is_identifier;
use ruff_python_trivia::CommentRanges;
use ruff_source_file::LineRanges;
use ruff_text_size::{Ranged, TextRange, TextSize};

use crate::checkers::ast::Checker;
use crate::codes::Category;
use crate::{Applicability, Edit, Fix, FixAvailability, Violation};

/// ## What it does
/// Checks for `NamedTuple` declarations that use functional syntax.
///
/// ## Why is this bad?
/// `NamedTuple` subclasses can be defined either through a functional syntax
/// (`Foo = NamedTuple(...)`) or a class syntax (`class Foo(NamedTuple): ...`).
///
/// The class syntax is more readable and generally preferred over the
/// functional syntax, which exists primarily for backwards compatibility
/// with `collections.namedtuple`.
///
/// ## Example
/// ```python
/// from typing import NamedTuple
///
/// Foo = NamedTuple("Foo", [("a", int), ("b", str)])
/// ```
///
/// Use instead:
/// ```python
/// from typing import NamedTuple
///
///
/// class Foo(NamedTuple):
///     a: int
///     b: str
/// ```
///
/// ## Fix safety
/// This rule's fix is marked as unsafe if there are any comments within the
/// range of the `NamedTuple` definition, as these will be dropped by the
/// autofix.
///
/// ## References
/// - [Python documentation: `typing.NamedTuple`](https://docs.python.org/3/library/typing.html#typing.NamedTuple)
#[derive(ViolationMetadata)]
#[violation_metadata(stable_since = "v0.0.155", category = Category::Style)]
pub(crate) struct ConvertNamedTupleFunctionalToClass {
    name: String,
}

impl Violation for ConvertNamedTupleFunctionalToClass {
    const FIX_AVAILABILITY: FixAvailability = FixAvailability::Sometimes;

    #[derive_message_formats]
    fn message(&self) -> String {
        let ConvertNamedTupleFunctionalToClass { name } = self;
        format!("Convert `{name}` from `NamedTuple` functional to class syntax")
    }

    fn fix_title(&self) -> Option<String> {
        let ConvertNamedTupleFunctionalToClass { name } = self;

        Some(format!("Convert `{name}` to class syntax"))
    }
}

/// UP014
pub(crate) fn convert_named_tuple_functional_to_class(
    checker: &Checker,
    stmt: &Stmt,
    targets: &[Expr],
    value: &Expr,
) {
    let Some((typename, args, keywords, base_class)) =
        match_named_tuple_assign(targets, value, checker.semantic())
    else {
        return;
    };

    let (fields, list_items) = match (args, keywords) {
        // Ex) `NamedTuple("MyType")`
        ([_typename], []) => (
            Suite::from([Stmt::Pass(ast::StmtPass {
                range: TextRange::default(),
                node_index: ruff_python_ast::AtomicNodeIndex::NONE,
            })]),
            None,
        ),
        // Ex) `NamedTuple("MyType", [("a", int), ("b", str)])`
        ([_typename, fields_arg], []) => {
            if let Some(list_expr) = fields_arg.as_list_expr() {
                if let Some(fields) = create_fields_from_fields_arg(fields_arg) {
                    (fields, Some(list_expr))
                } else {
                    debug!("Skipping `NamedTuple` \"{typename}\": unable to parse fields");
                    return;
                }
            } else {
                debug!("Skipping `NamedTuple` \"{typename}\": unable to parse fields");
                return;
            }
        }
        // Ex) `NamedTuple("MyType", a=int, b=str)`
        ([_typename], keywords) => {
            if let Some(fields) = create_fields_from_keywords(keywords) {
                (fields, None)
            } else {
                debug!("Skipping `NamedTuple` \"{typename}\": unable to parse keywords");
                return;
            }
        }
        // Ex) `NamedTuple()`
        _ => {
            debug!("Skipping `NamedTuple` \"{typename}\": mixed fields and keywords");
            return;
        }
    };

    let mut diagnostic = checker.report_diagnostic(
        ConvertNamedTupleFunctionalToClass {
            name: typename.to_string(),
        },
        stmt.range(),
    );
    // TODO(charlie): Preserve indentation, to remove the first-column requirement.
    if checker.locator().is_at_start_of_line(stmt.start()) {
        diagnostic.set_fix(convert_to_class(FixParams {
            stmt,
            typename,
            body: fields,
            base_class,
            generator: checker.generator(),
            comment_ranges: checker.comment_ranges(),
            source: checker.locator().contents(),
            list_items,
        }));
    }
}

/// Return the typename, args, keywords, and base class.
fn match_named_tuple_assign<'a>(
    targets: &'a [Expr],
    value: &'a Expr,
    semantic: &SemanticModel,
) -> Option<(&'a str, &'a [Expr], &'a [Keyword], &'a Expr)> {
    let [Expr::Name(ast::ExprName { id: typename, .. })] = targets else {
        return None;
    };
    let Expr::Call(ast::ExprCall {
        func,
        arguments: Arguments { args, keywords, .. },
        range_start: _,
        node_index: _,
    }) = value
    else {
        return None;
    };
    if !semantic.match_typing_expr(func, "NamedTuple") {
        return None;
    }
    Some((typename, args, keywords, func))
}

/// Generate a [`Stmt::AnnAssign`] representing the provided field definition.
fn create_field_assignment_stmt(field: Name, annotation: &Expr) -> Stmt {
    ast::StmtAnnAssign {
        target: Box::new(
            ast::ExprName {
                id: field,
                ctx: ExprContext::Load,
                range: TextRange::default(),
                node_index: ruff_python_ast::AtomicNodeIndex::NONE,
            }
            .into(),
        ),
        annotation: Box::new(annotation.clone()),
        value: None,
        simple: true,
        range: TextRange::default(),
        node_index: ruff_python_ast::AtomicNodeIndex::NONE,
    }
    .into()
}

/// Create a list of field assignments from the `NamedTuple` fields argument.
fn create_fields_from_fields_arg(fields: &Expr) -> Option<Suite> {
    let fields = fields.as_list_expr()?;
    if fields.is_empty() {
        let node = Stmt::Pass(ast::StmtPass {
            range: TextRange::default(),
            node_index: ruff_python_ast::AtomicNodeIndex::NONE,
        });
        Some(Suite::from([node]))
    } else {
        fields
            .iter()
            .map(|field| {
                let ast::ExprTuple { elts, .. } = field.as_tuple_expr()?;
                let [field, annotation] = elts.as_slice() else {
                    return None;
                };
                if annotation.is_starred_expr() {
                    return None;
                }
                let ast::ExprStringLiteral { value: field, .. } = field.as_string_literal_expr()?;
                if !is_identifier(field.to_str()) {
                    return None;
                }
                if is_dunder(field.to_str()) {
                    return None;
                }
                Some(create_field_assignment_stmt(
                    Name::new(field.to_str()),
                    annotation,
                ))
            })
            .collect()
    }
}

/// Create a list of field assignments from the `NamedTuple` keyword arguments.
fn create_fields_from_keywords(keywords: &[Keyword]) -> Option<Suite> {
    keywords
        .iter()
        .map(|keyword| {
            keyword
                .arg
                .as_ref()
                .map(|field| create_field_assignment_stmt(field.id.clone(), &keyword.value))
        })
        .collect()
}

/// Generate a `StmtKind:ClassDef` statement based on the provided body and
/// keywords.
fn create_class_def_stmt(typename: &str, body: Suite, base_class: &Expr) -> Stmt {
    ast::StmtClassDef {
        name: Identifier::new(typename.to_string(), TextRange::default()),
        arguments: Some(Box::new(Arguments {
            args: Box::from([base_class.clone()]),
            keywords: std::iter::empty().collect(),
            range: TextRange::default(),
            node_index: ruff_python_ast::AtomicNodeIndex::NONE,
        })),
        body,
        type_params: None,
        decorator_list: DecoratorList::new(),
        range: TextRange::default(),
        node_index: ruff_python_ast::AtomicNodeIndex::NONE,
    }
    .into()
}

struct FixParams<'a> {
    stmt: &'a Stmt,
    typename: &'a str,
    body: Suite,
    base_class: &'a Expr,
    generator: Generator<'a>,
    comment_ranges: &'a CommentRanges,
    source: &'a str,
    list_items: Option<&'a ast::ExprList>,
}

/// Generate a `Fix` to convert a `NamedTuple` assignment to a class definition.
fn convert_to_class(params: FixParams<'_>) -> Fix {
    let applicability = if params.comment_ranges.intersects(params.stmt.range()) {
        Applicability::Unsafe
    } else {
        Applicability::Safe
    };

    let mut output = params.generator.stmt(&create_class_def_stmt(
        params.typename,
        params.body,
        params.base_class,
    ));

    if let Some(list_expr) = params.list_items.filter(|l| !l.elts.is_empty()) {
        let all_comments = params.comment_ranges.comments_in_range(list_expr.range());
        if !all_comments.is_empty() {
            let item_ranges: Vec<_> = list_expr
                .elts
                .iter()
                .map(|item| (item.start(), item.end()))
                .collect();
            output = reattach_comments(&output, &item_ranges, all_comments, params.source);
        }
    }

    Fix::applicable_edit(
        Edit::range_replacement(output, params.stmt.range()),
        applicability,
    )
}

/// Reinsert comments from an original list literal into a generated class body,
/// attaching each comment to the field it was originally adjacent to.
fn reattach_comments(
    output: &str,
    item_ranges: &[(TextSize, TextSize)],
    all_comments: &[TextRange],
    source: &str,
) -> String {
    let mut trailing: Vec<Option<&str>> = vec![None; item_ranges.len()];
    let mut leading: Vec<Vec<&str>> = vec![Vec::new(); item_ranges.len()];
    let mut trailing_own_line: Vec<Vec<&str>> = vec![Vec::new(); item_ranges.len()];

    for comment_range in all_comments {
        let start = comment_range.start();
        let line_start = source.line_start(start);
        let text = &source[*comment_range];

        if let Some(i) = item_ranges
            .iter()
            .position(|&(_, end)| line_start <= end && start >= end)
        {
            trailing[i].get_or_insert(text);
        } else if let Some(i) = item_ranges.iter().position(|&(s, _)| start < s) {
            leading[i].push(text);
        } else if start > item_ranges[item_ranges.len() - 1].1 {
            trailing_own_line[item_ranges.len() - 1].push(text);
        }
    }

    let mut lines = output.lines();
    let header = lines.next().unwrap_or_default().to_string();
    let mut new_lines = Vec::with_capacity(item_ranges.len() * 2 + 1);
    new_lines.push(header);

    for (field_idx, line) in lines.enumerate() {
        let indent_str = " ".repeat(line.len() - line.trim_start().len());

        new_lines.extend(
            leading[field_idx]
                .iter()
                .map(|c| format!("{indent_str}{c}")),
        );

        let mut line = line.to_string();
        if let Some(c) = trailing[field_idx] {
            if !line.ends_with(' ') {
                line.push(' ');
            }
            line.push_str(c);
        }
        new_lines.push(line);

        new_lines.extend(
            trailing_own_line[field_idx]
                .iter()
                .map(|c| format!("{indent_str}{c}")),
        );
    }

    new_lines.join("\n")
}
