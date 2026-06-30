from bpmncwpverify.core.feel_tree import (
    AndNode,
    BoolLiteralNode,
    ChooseNode,
    ComparisonOperatorNode,
    IfNode,
    ListNode,
    OrNode,
    QualifiedNameNode,
    TripleNode,
    XOrNode,
)
from bpmncwpverify.visitors.feel_to_promela_visitor import FeelToPromelaVisitor


def test_and() -> None:
    node = AndNode(BoolLiteralNode("true"), QualifiedNameNode("something"))
    visitor = FeelToPromelaVisitor()

    node.accept(visitor)

    assert str(visitor.promela) == "true && something"


def test_or() -> None:
    node = OrNode(QualifiedNameNode("x"), QualifiedNameNode("y"))
    visitor = FeelToPromelaVisitor()

    node.accept(visitor)

    assert str(visitor.promela) == "true || something"


def test_xor() -> None:
    node = XOrNode(QualifiedNameNode("x"), QualifiedNameNode("y"))
    visitor = FeelToPromelaVisitor()

    node.accept(visitor)

    assert str(visitor.promela) == ""


def test_if() -> None:
    node = IfNode(
        BoolLiteralNode("true"),
        QualifiedNameNode("missing"),
        QualifiedNameNode("found"),
    )
    visitor = FeelToPromelaVisitor()

    node.accept(visitor)

    assert str(visitor.promela) == "if\n\t:: true -> missing\n\t:: else -> found\nfi"


def test_choose() -> None:
    node = ChooseNode(
        ListNode([QualifiedNameNode("missing"), QualifiedNameNode("found")])
    )
    visitor = FeelToPromelaVisitor()

    node.accept(visitor)

    assert str(visitor.promela) == "if\n:: True -> missing\n::True -> found\nfi"


def test_triple_with_if_and_choose() -> None:
    node = TripleNode(
        QualifiedNameNode("blackBox"),
        ListNode([QualifiedNameNode("uuvComms")]),
        IfNode(
            ComparisonOperatorNode(
                QualifiedNameNode("uuvComms"), QualifiedNameNode("wait")
            ),
            QualifiedNameNode("missing"),
            ChooseNode(
                ListNode([QualifiedNameNode("missing"), QualifiedNameNode("found")])
            ),
        ),
    )
    visitor = FeelToPromelaVisitor()

    node.accept(visitor)

    assert (
        str(visitor.promela)
        == "if\n:: uuvComms == wait -> blackBox = missing\n:: else ->\n\tif\n\t:: true -> blackBox = missing\n\t:: true -> blackBox = found\n\tfi\nfi"
    )
