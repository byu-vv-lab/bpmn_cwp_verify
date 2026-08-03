from returns.maybe import Some

from bpmncwpverify.core.feel_tree import (
    AddNode,
    AndNode,
    BoolLiteralNode,
    ChooseNode,
    EqualNode,
    IfNode,
    ListNode,
    MultiplyNode,
    NotNode,
    NumberLiteralNode,
    OrNode,
    QualifiedNameNode,
    TripleListNode,
    TripleNode,
    XOrNode,
)
from bpmncwpverify.visitors.feel_to_promela_visitor import FeelToPromelaVisitor


def test_list() -> None:
    node = ListNode(
        [NumberLiteralNode("2"), NumberLiteralNode("1"), NumberLiteralNode("0")]
    )
    visitor = FeelToPromelaVisitor()

    node.accept(visitor)

    assert str(visitor.promela) == "{2, 1, 0}"


def test_add() -> None:
    node = AddNode(NumberLiteralNode("2"), QualifiedNameNode("3"))
    visitor = FeelToPromelaVisitor()

    node.accept(visitor)

    assert str(visitor.promela) == "(2 + 3)"


def test_multiply_and_add() -> None:
    node = AddNode(
        NumberLiteralNode("5"),
        MultiplyNode(NumberLiteralNode("2"), QualifiedNameNode("3")),
    )
    visitor = FeelToPromelaVisitor()

    node.accept(visitor)

    assert str(visitor.promela) == "(5 + (2 * 3))"


def test_and() -> None:
    node = AndNode(BoolLiteralNode("true"), QualifiedNameNode("something"))
    visitor = FeelToPromelaVisitor()

    node.accept(visitor)

    assert str(visitor.promela) == "(true && something)"


def test_or() -> None:
    node = OrNode(QualifiedNameNode("x"), QualifiedNameNode("y"))
    visitor = FeelToPromelaVisitor()

    node.accept(visitor)

    assert str(visitor.promela) == "(x || y)"


def test_xor() -> None:
    node = XOrNode(QualifiedNameNode("X"), QualifiedNameNode("Y"))
    visitor = FeelToPromelaVisitor()

    node.accept(visitor)

    assert str(visitor.promela) == "(X && !Y || !X && Y)"


def test_or_and() -> None:
    node = OrNode(
        AndNode(QualifiedNameNode("this"), QualifiedNameNode("that")),
        XOrNode(QualifiedNameNode("this"), QualifiedNameNode("notthis")),
    )
    visitor = FeelToPromelaVisitor()

    node.accept(visitor)

    assert (
        str(visitor.promela)
        == "((this && that) || (this && !notthis || !this && notthis))"
    )


def test_equal_comparision_with_chooose() -> None:
    node = EqualNode(
        QualifiedNameNode("b"),
        ChooseNode(ListNode([BoolLiteralNode("true"), BoolLiteralNode("false")])),
    )

    visitor = FeelToPromelaVisitor("0")

    assert isinstance(node.right, ChooseNode)
    node.right.choices.type = Some("bool")

    node.accept(visitor)

    assert (
        str(visitor.choose)
        == "mtype:bool choose_0_0[2] = {true, false}\nbyte choose_0_0_i = 0\n"
    )
    assert str(visitor.selects) == "atomic{select(choose_0_0_i : 0..1)}\n"
    assert str(visitor.promela) == "(b == choose_0_0[choose_0_0_i])"


def test_if() -> None:
    node = IfNode(
        BoolLiteralNode("true"),
        QualifiedNameNode("missing"),
        QualifiedNameNode("found"),
    )
    visitor = FeelToPromelaVisitor()

    node.accept(visitor)

    assert str(visitor.promela) == "(true -> missing : found)"


def test_not() -> None:
    node = NotNode(BoolLiteralNode("true"))
    visitor = FeelToPromelaVisitor()

    node.accept(visitor)

    assert str(visitor.promela) == "!true"


def test_true_and_not_false() -> None:
    node = AndNode(BoolLiteralNode("true"), NotNode(BoolLiteralNode("false")))
    visitor = FeelToPromelaVisitor()

    node.accept(visitor)

    assert str(visitor.promela) == "(true && !false)"


def test_choose() -> None:
    node = ChooseNode(
        ListNode(
            [
                QualifiedNameNode("standby"),
                QualifiedNameNode("waiting"),
                QualifiedNameNode("off"),
            ]
        )
    )
    node.choices.type = Some("commsState")
    visitor = FeelToPromelaVisitor("0")

    node.accept(visitor)

    assert (
        str(visitor.choose)
        == "mtype:commsState choose_0_0[3] = {standby, waiting, off}\nbyte choose_0_0_i = 0\n"
    )
    assert str(visitor.selects) == "atomic{select(choose_0_0_i : 0..2)}\n"
    assert str(visitor.promela) == "choose_0_0[choose_0_0_i]"


def test_triple_with_if() -> None:
    node = TripleNode(
        QualifiedNameNode("blackBox"),
        ListNode([QualifiedNameNode("uuvComms")]),
        IfNode(
            EqualNode(QualifiedNameNode("uuvComms"), QualifiedNameNode("wait")),
            QualifiedNameNode("missing"),
            QualifiedNameNode("found"),
        ),
    )
    visitor = FeelToPromelaVisitor()

    node.accept(visitor)

    assert str(visitor.promela) == "blackBox = ((uuvComms == wait) -> missing : found)"


def test_triple_with_choose() -> None:
    node = TripleNode(
        QualifiedNameNode("comms"),
        ListNode([QualifiedNameNode("blackBox")]),
        ChooseNode(
            ListNode(
                [
                    QualifiedNameNode("standby"),
                    QualifiedNameNode("waiting"),
                    QualifiedNameNode("off"),
                ]
            )
        ),
    )

    assert isinstance(node.value, ChooseNode)
    node.value.choices.type = Some("commsState")

    visitor = FeelToPromelaVisitor("0")

    node.accept(visitor)

    assert (
        str(visitor.choose)
        == "mtype:commsState choose_0_0[3] = {standby, waiting, off}\nbyte choose_0_0_i = 0\n"
    )
    assert str(visitor.selects) == "atomic{select(choose_0_0_i : 0..2)}\n"
    assert str(visitor.promela) == "comms = choose_0_0[choose_0_0_i]"


def test_triple() -> None:
    node = TripleNode(
        QualifiedNameNode("uuvComms"), ListNode([]), QualifiedNameNode("sent")
    )

    visitor = FeelToPromelaVisitor()

    node.accept(visitor)

    assert str(visitor.promela) == "uuvComms = sent"


def test_if_equal_to_self() -> None:
    node = TripleNode(
        QualifiedNameNode("conditions"),
        ListNode([QualifiedNameNode("risk"), QualifiedNameNode("conditions")]),
        IfNode(
            EqualNode(QualifiedNameNode("risk"), QualifiedNameNode("acceptable")),
            QualifiedNameNode("same"),
            QualifiedNameNode("conditions"),
        ),
    )

    visitor = FeelToPromelaVisitor()

    node.accept(visitor)

    assert (
        str(visitor.promela)
        == "conditions = ((risk == acceptable) -> same : conditions)"
    )


def test_input_if_choose() -> None:
    # (conditions, [blackBox, conditions], if blackBox = missing then choose [same, changed] else conditions)
    node = TripleNode(
        QualifiedNameNode("conditions"),
        ListNode([QualifiedNameNode("blackBox"), QualifiedNameNode("conditions")]),
        IfNode(
            EqualNode(QualifiedNameNode("blackBox"), QualifiedNameNode("missing")),
            ChooseNode(
                ListNode([QualifiedNameNode("same"), QualifiedNameNode("changed")])
            ),
            QualifiedNameNode("conditions"),
        ),
    )

    visitor = FeelToPromelaVisitor("0")
    assert isinstance(node.value, IfNode)
    assert isinstance(node.value.thendo, ChooseNode)
    node.value.thendo.choices.type = Some("Cond")

    node.accept(visitor)

    assert (
        str(visitor.choose)
        == "mtype:Cond choose_0_0[2] = {same, changed}\nbyte choose_0_0_i = 0\n"
    )
    assert str(visitor.selects) == "atomic{select(choose_0_0_i : 0..1)}\n"
    assert (
        str(visitor.promela)
        == "conditions = ((blackBox == missing) -> choose_0_0[choose_0_0_i] : conditions)"
    )


def test_input_if_then_choose_else() -> None:
    # (conditions, [blackBox, conditions], if blackBox = missing then choose [same, changed] else choose [same, notgood])
    node = TripleNode(
        QualifiedNameNode("conditions"),
        ListNode([QualifiedNameNode("blackBox"), QualifiedNameNode("conditions")]),
        IfNode(
            EqualNode(QualifiedNameNode("blackBox"), QualifiedNameNode("missing")),
            ChooseNode(
                ListNode([QualifiedNameNode("same"), QualifiedNameNode("changed")])
            ),
            ChooseNode(
                ListNode([QualifiedNameNode("same"), QualifiedNameNode("notgood")])
            ),
        ),
    )

    visitor = FeelToPromelaVisitor("activity")
    assert isinstance(node.value, IfNode)
    assert isinstance(node.value.thendo, ChooseNode)
    assert isinstance(node.value.elsedo, ChooseNode)
    node.value.thendo.choices.type = Some("Cond")
    node.value.elsedo.choices.type = Some("Cond")

    node.accept(visitor)

    assert (
        str(visitor.choose)
        == "mtype:Cond choose_activity_0[2] = {same, changed}\nbyte choose_activity_0_i = 0\nmtype:Cond choose_activity_1[2] = {same, notgood}\nbyte choose_activity_1_i = 0\n"
    )
    assert (
        str(visitor.selects)
        == "atomic{select(choose_activity_0_i : 0..1)}\natomic{select(choose_activity_1_i : 0..1)}\n"
    )
    assert (
        str(visitor.promela)
        == "conditions = ((blackBox == missing) -> choose_activity_0[choose_activity_0_i] : choose_activity_1[choose_activity_1_i])"
    )


def test_triple_list() -> None:
    node = TripleListNode(
        [
            TripleNode(
                QualifiedNameNode("uuvComms"), ListNode([]), QualifiedNameNode("sent")
            ),
            TripleNode(QualifiedNameNode("x"), ListNode([]), QualifiedNameNode("y")),
        ]
    )
    visitor = FeelToPromelaVisitor()

    node.accept(visitor)

    assert isinstance(node.triples[0], TripleNode)
    assert isinstance(node.triples[1], TripleNode)
    assert str(visitor.promela) == "uuvComms = sent\nx = y\n"
