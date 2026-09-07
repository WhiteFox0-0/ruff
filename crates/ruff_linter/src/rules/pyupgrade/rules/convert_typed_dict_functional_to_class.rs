use ruff_macros::{ViolationMetadata, derive_message_formats};
use ruff_python_ast::{
    self as ast, Arguments, Expr, ExprContext, Identifier, Keyword, Stmt, Suite,
};
use ruff_python_codegen::Generator;
use ruff_python_semantic::SemanticModel;
use ruff_python_stdlib::identifiers::is_identifier;
use ruff_python_trivia::CommentRanges;
use ruff_source_file::LineRanges;
use ruff_text_size::{Ranged, TextRange};

use crate::checkers::ast::Checker;
use crate::codes::Category;
use crate::{Applicability, Edit, Fix, FixAvailability, Violation};

/// ## What it does
/// Checks for `TypedDict` declarations that use functional syntax.
///
/// ## Why is this bad?
/// `TypedDict` types can be defined either through a functional syntax
/// (`Foo = TypedDict(...)`) or a class syntax (`class Foo(TypedDict): ...`).
///
/// The class syntax is more readable and generally preferred over the
/// functional syntax.
///
/// Nonetheless, there are some situations in which it is impossible to use
/// the class-based syntax. This rule will not apply to those cases. Namely,
/// it is impossible to use the class-based syntax if any `TypedDict` fields are:
/// - Not valid [python identifiers] (for example, `@x`)
/// - [Python keywords] such as `in`
/// - [Private names] such as `__id` that would undergo [name mangling] at runtime
///   if the class-based syntax was used
/// - [Dunder names] such as `__int__` that can confuse type checkers if they're used
///   with the class-based syntax.
///
/// ## Example
/// ```python
/// from typing import TypedDict
///
/// Foo = TypedDict("Foo", {"a": int, "b": str})
/// ```
///
/// Use instead:
/// ```python
/// from typing import TypedDict
///
///
/// class Foo(TypedDict):
///     a: int
///     b: str
/// ```
///
/// ## Fix safety
/// This rule's fix is marked as unsafe if there are any comments within the
/// range of the `TypedDict` definition, as these will be dropped by the
/// autofix.
///
/// ## References
/// - [Python documentation: `typing.TypedDict`](https://docs.python.org/3/library/typing.html#typing.TypedDict)
///
/// [Private names]: https://docs.python.org/3/tutorial/classes.html#private-variables
/// [name mangling]: https://docs.python.org/3/reference/expressions.html#private-name-mangling
/// [python identifiers]: https://docs.python.org/3/reference/lexical_analysis.html#identifiers
/// [Python keywords]: https://docs.python.org/3/reference/lexical_analysis.html#keywords
/// [Dunder names]: https://docs.python.org/3/reference/lexical_analysis.html#reserved-classes-of-identifiers
#[derive(ViolationMetadata)]
#[violation_metadata(stable_since = "v0.0.155", category = Category::Pedantic)]
pub(crate) struct ConvertTypedDictFunctionalToClass {
    name: String,
}

impl Violation for ConvertTypedDictFunctionalToClass {
    const FIX_AVAILABILITY: FixAvailability = FixAvailability::Sometimes;

    #[derive_message_formats]
    fn message(&self) -> String {
        let ConvertTypedDictFunctionalToClass { name } = self;
        format!("Convert `{name}` from `TypedDict` functional to class syntax")
    }

    fn fix_title(&self) -> Option<String> {
        let ConvertTypedDictFunctionalToClass { name } = self;
        Some(format!("Convert `{name}` to class syntax"))
    }
}

/// UP013
pub(crate) fn convert_typed_dict_functional_to_class(
    checker: &Checker,
    stmt: &Stmt,
    targets: &[Expr],
    value: &Expr,
) {
    let Some((class_name, arguments, base_class)) =
        match_typed_dict_assign(targets, value, checker.semantic())
    else {
        return;
    };

    let Some(TypedDictFields {
        body,
        total_keyword,
        dict_items,
    }) = match_fields_and_total(arguments)
    else {
        return;
    };

    let mut diagnostic = checker.report_diagnostic(
        ConvertTypedDictFunctionalToClass {
            name: class_name.to_string(),
        },
        stmt.range(),
    );
    // TODO(charlie): Preserve indentation, to remove the first-column requirement.
    if checker.locator().is_at_start_of_line(stmt.start()) {
        diagnostic.set_fix(convert_to_class(FixParams {
            stmt,
            class_name,
            body,
            total_keyword,
            base_class,
            generator: checker.generator(),
            comment_ranges: checker.comment_ranges(),
            source: checker.locator().contents(),
            dict_items,
        }));
    }
}

/// Return the class name, arguments, keywords and base class for a `TypedDict`
/// assignment.
fn match_typed_dict_assign<'a>(
    targets: &'a [Expr],
    value: &'a Expr,
    semantic: &SemanticModel,
) -> Option<(&'a str, &'a Arguments, &'a Expr)> {
    let [Expr::Name(ast::ExprName { id: class_name, .. })] = targets else {
        return None;
    };
    let Expr::Call(ast::ExprCall {
        func,
        arguments,
        range_start: _,
        node_index: _,
    }) = value
    else {
        return None;
    };
    if !semantic.match_typing_expr(func, "TypedDict") {
        return None;
    }
    Some((class_name, arguments, func))
}

/// Generate a [`Stmt::AnnAssign`] representing the provided field definition.
fn create_field_assignment_stmt(field: &str, annotation: &Expr) -> Stmt {
    ast::StmtAnnAssign {
        target: Box::new(
            ast::ExprName {
                id: field.into(),
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

/// Generate a `StmtKind:ClassDef` statement based on the provided body, keywords, and base class.
fn create_class_def_stmt(
    class_name: &str,
    body: Suite,
    total_keyword: Option<&Keyword>,
    base_class: &Expr,
) -> Stmt {
    ast::StmtClassDef {
        name: Identifier::new(class_name.to_string(), TextRange::default()),
        arguments: Some(Box::new(Arguments {
            args: Box::from([base_class.clone()]),
            keywords: match total_keyword {
                Some(keyword) => std::iter::once(keyword.clone()).collect(),
                None => std::iter::empty().collect(),
            },
            range: TextRange::default(),
            node_index: ruff_python_ast::AtomicNodeIndex::NONE,
        })),
        body,
        type_params: None,
        decorator_list: ast::DecoratorList::new(),
        range: TextRange::default(),
        node_index: ruff_python_ast::AtomicNodeIndex::NONE,
    }
    .into()
}

fn fields_from_dict_literal(items: &[ast::DictItem]) -> Option<Suite> {
    if items.is_empty() {
        let node = Stmt::Pass(ast::StmtPass {
            range: TextRange::default(),
            node_index: ruff_python_ast::AtomicNodeIndex::NONE,
        });
        Some(Suite::from([node]))
    } else {
        items
            .iter()
            .map(|ast::DictItem { key, value }| match key {
                Some(Expr::StringLiteral(ast::ExprStringLiteral { value: field, .. })) => {
                    if !is_identifier(field.to_str()) {
                        return None;
                    }
                    // Converting TypedDict to class-based syntax is not safe if fields contain
                    // private or dunder names, because private names will be mangled and dunder
                    // names can confuse type checkers.
                    if field.to_str().starts_with("__") {
                        return None;
                    }
                    Some(create_field_assignment_stmt(field.to_str(), value))
                }
                _ => None,
            })
            .collect()
    }
}

fn fields_from_dict_call(func: &Expr, keywords: &[Keyword]) -> Option<Suite> {
    let ast::ExprName { id, .. } = func.as_name_expr()?;
    if id != "dict" {
        return None;
    }

    if keywords.is_empty() {
        let node = Stmt::Pass(ast::StmtPass {
            range: TextRange::default(),
            node_index: ruff_python_ast::AtomicNodeIndex::NONE,
        });
        Some(Suite::from([node]))
    } else {
        fields_from_keywords(keywords)
    }
}

// Deprecated in Python 3.11, removed in Python 3.13.
fn fields_from_keywords(keywords: &[Keyword]) -> Option<Suite> {
    if keywords.is_empty() {
        let node = Stmt::Pass(ast::StmtPass {
            range: TextRange::default(),
            node_index: ruff_python_ast::AtomicNodeIndex::NONE,
        });
        return Some(Suite::from([node]));
    }

    keywords
        .iter()
        .map(|keyword| {
            keyword
                .arg
                .as_ref()
                .map(|field| create_field_assignment_stmt(field, &keyword.value))
        })
        .collect()
}

struct TypedDictFields<'a> {
    body: Suite,
    total_keyword: Option<&'a Keyword>,
    dict_items: Option<(&'a [ast::DictItem], TextRange)>,
}

/// Match the fields and `total` keyword from a `TypedDict` call.
fn match_fields_and_total(arguments: &Arguments) -> Option<TypedDictFields<'_>> {
    match (&*arguments.args, &*arguments.keywords) {
        // Ex) `TypedDict("MyType", {"a": int, "b": str})`
        ([_typename, fields], [..]) => {
            let total = arguments.find_keyword("total");
            match fields {
                Expr::Dict(ast::ExprDict {
                    items,
                    range,
                    node_index: _,
                }) => Some(TypedDictFields {
                    body: fields_from_dict_literal(items)?,
                    total_keyword: total,
                    dict_items: Some((items, *range)),
                }),
                Expr::Call(ast::ExprCall {
                    func,
                    arguments: Arguments { keywords, .. },
                    range_start: _,
                    node_index: _,
                }) => Some(TypedDictFields {
                    body: fields_from_dict_call(func, keywords)?,
                    total_keyword: total,
                    dict_items: None,
                }),
                _ => None,
            }
        }
        // Ex) `TypedDict("MyType")`
        ([_typename], []) => {
            let node = Stmt::Pass(ast::StmtPass {
                range: TextRange::default(),
                node_index: ruff_python_ast::AtomicNodeIndex::NONE,
            });
            Some(TypedDictFields {
                body: Suite::from([node]),
                total_keyword: None,
                dict_items: None,
            })
        }
        // Ex) `TypedDict("MyType", a=int, b=str)`
        ([_typename], fields) => Some(TypedDictFields {
            body: fields_from_keywords(fields)?,
            total_keyword: None,
            dict_items: None,
        }),
        // Ex) `TypedDict()`
        _ => None,
    }
}

struct FixParams<'a> {
    stmt: &'a Stmt,
    class_name: &'a str,
    body: Suite,
    total_keyword: Option<&'a Keyword>,
    base_class: &'a Expr,
    generator: Generator<'a>,
    comment_ranges: &'a CommentRanges,
    source: &'a str,
    dict_items: Option<(&'a [ast::DictItem], TextRange)>,
}

/// Generate a `Fix` to convert a `TypedDict` from functional to class.
fn convert_to_class(params: FixParams<'_>) -> Fix {
    let applicability = if params.comment_ranges.intersects(params.stmt.range()) {
        Applicability::Unsafe
    } else {
        Applicability::Safe
    };

    let mut output = params.generator.stmt(&create_class_def_stmt(
        params.class_name,
        params.body,
        params.total_keyword,
        params.base_class,
    ));

    if let Some(with_comments) = params
        .dict_items
        .filter(|(items, _)| !items.is_empty())
        .and_then(|(items, dict_range)| {
            let comments = params.comment_ranges.comments_in_range(dict_range);
            (!comments.is_empty())
                .then(|| reattach_comments(&output, items, comments, params.source))
        })
    {
        output = with_comments;
    }

    Fix::applicable_edit(
        Edit::range_replacement(output, params.stmt.range()),
        applicability,
    )
}

/// Reinsert comments from the original dict literal into the generated class body,
/// attaching each to the field it was originally next to.
fn reattach_comments(
    output: &str,
    items: &[ast::DictItem],
    all_comments: &[TextRange],
    source: &str,
) -> String {
    let mut trailing: Vec<Option<&str>> = vec![None; items.len()];
    let mut leading: Vec<Vec<&str>> = vec![Vec::new(); items.len()];
    let mut trailing_own_line: Vec<Vec<&str>> = vec![Vec::new(); items.len()];

    for comment_range in all_comments {
        let start = comment_range.start();
        let line_start = source.line_start(start);
        let text = &source[*comment_range];

        if let Some(i) = items
            .iter()
            .position(|item| line_start <= item.value.end() && start >= item.value.end())
        {
            trailing[i].get_or_insert(text);
        } else if let Some(i) = items.iter().position(|item| start < item.start()) {
            leading[i].push(text);
        } else if start > items[items.len() - 1].value.end() {
            trailing_own_line[items.len() - 1].push(text);
        }
    }

    let mut lines = output.lines();
    let header = lines.next().unwrap_or_default().to_string();
    let mut new_lines = Vec::with_capacity(items.len() * 2 + 1);
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
