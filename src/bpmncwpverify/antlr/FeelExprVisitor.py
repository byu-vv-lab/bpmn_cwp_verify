# Generated from antlr/FeelExpr.g4 by ANTLR 4.13.2
#type: ignore
from antlr4 import *
if "." in __name__:
    from .FeelExprParser import FeelExprParser
else:
    from FeelExprParser import FeelExprParser

# This class defines a complete generic visitor for a parse tree produced by FeelExprParser.

class FeelExprVisitor(ParseTreeVisitor):

    # Visit a parse tree produced by FeelExprParser#compilation_unit.
    def visitCompilation_unitContext(self, ctx:FeelExprParser.Compilation_unitContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#expressionTextual.
    def visitExpressionTextualContext(self, ctx:FeelExprParser.ExpressionTextualContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#textualExpression.
    def visitTextualExpression(self, ctx:FeelExprParser.TextualExpressionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#parametersEmpty.
    def visitParametersEmpty(self, ctx:FeelExprParser.ParametersEmptyContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#parametersNamed.
    def visitParametersNamed(self, ctx:FeelExprParser.ParametersNamedContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#parametersPositional.
    def visitParametersPositional(self, ctx:FeelExprParser.ParametersPositionalContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#namedParameters.
    def visitNamedParameters(self, ctx:FeelExprParser.NamedParametersContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#namedParameter.
    def visitNamedParameter(self, ctx:FeelExprParser.NamedParameterContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#positionalParameters.
    def visitPositionalParameters(self, ctx:FeelExprParser.PositionalParametersContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#forExpression.
    def visitForExpression(self, ctx:FeelExprParser.ForExpressionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#iterationContexts.
    def visitIterationContexts(self, ctx:FeelExprParser.IterationContextsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#iterationContext.
    def visitIterationContext(self, ctx:FeelExprParser.IterationContextContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#ifExpression.
    def visitIfExpression(self, ctx:FeelExprParser.IfExpressionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#quantExprSome.
    def visitQuantExprSome(self, ctx:FeelExprParser.QuantExprSomeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#quantExprEvery.
    def visitQuantExprEvery(self, ctx:FeelExprParser.QuantExprEveryContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#listType.
    def visitListType(self, ctx:FeelExprParser.ListTypeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#rangeType.
    def visitRangeType(self, ctx:FeelExprParser.RangeTypeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#contextType.
    def visitContextType(self, ctx:FeelExprParser.ContextTypeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#qnType.
    def visitQnType(self, ctx:FeelExprParser.QnTypeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#functionType.
    def visitFunctionType(self, ctx:FeelExprParser.FunctionTypeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#list.
    def visitList(self, ctx:FeelExprParser.ListContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#functionDefinition.
    def visitFunctionDefinition(self, ctx:FeelExprParser.FunctionDefinitionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#formalParameters.
    def visitFormalParameters(self, ctx:FeelExprParser.FormalParametersContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#formalParameter.
    def visitFormalParameter(self, ctx:FeelExprParser.FormalParameterContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#context.
    def visitContext(self, ctx:FeelExprParser.ContextContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#contextEntries.
    def visitContextEntries(self, ctx:FeelExprParser.ContextEntriesContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#contextEntry.
    def visitContextEntry(self, ctx:FeelExprParser.ContextEntryContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#keyName.
    def visitKeyName(self, ctx:FeelExprParser.KeyNameContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#keyString.
    def visitKeyString(self, ctx:FeelExprParser.KeyStringContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#nameDefinition.
    def visitNameDefinition(self, ctx:FeelExprParser.NameDefinitionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#nameDefinitionWithEOF.
    def visitNameDefinitionWithEOF(self, ctx:FeelExprParser.NameDefinitionWithEOFContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#nameDefinitionTokens.
    def visitNameDefinitionTokens(self, ctx:FeelExprParser.NameDefinitionTokensContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#iterationNameDefinition.
    def visitIterationNameDefinition(self, ctx:FeelExprParser.IterationNameDefinitionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#iterationNameDefinitionTokens.
    def visitIterationNameDefinitionTokens(self, ctx:FeelExprParser.IterationNameDefinitionTokensContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#additionalNameSymbol.
    def visitAdditionalNameSymbol(self, ctx:FeelExprParser.AdditionalNameSymbolContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#condOr.
    def visitCondOr(self, ctx:FeelExprParser.CondOrContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#condOrAnd.
    def visitCondOrAnd(self, ctx:FeelExprParser.CondOrAndContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#condAndComp.
    def visitCondAndComp(self, ctx:FeelExprParser.CondAndCompContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#condAnd.
    def visitCondAnd(self, ctx:FeelExprParser.CondAndContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#compExpression.
    def visitCompExpression(self, ctx:FeelExprParser.CompExpressionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#compExpressionRel.
    def visitCompExpressionRel(self, ctx:FeelExprParser.CompExpressionRelContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#relExpressionBetween.
    def visitRelExpressionBetween(self, ctx:FeelExprParser.RelExpressionBetweenContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#relExpressionValue.
    def visitRelExpressionValue(self, ctx:FeelExprParser.RelExpressionValueContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#relExpressionTestList.
    def visitRelExpressionTestList(self, ctx:FeelExprParser.RelExpressionTestListContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#relExpressionAdd.
    def visitRelExpressionAdd(self, ctx:FeelExprParser.RelExpressionAddContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#relExpressionInstanceOf.
    def visitRelExpressionInstanceOf(self, ctx:FeelExprParser.RelExpressionInstanceOfContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#expressionList.
    def visitExpressionList(self, ctx:FeelExprParser.ExpressionListContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#addExpressionMult.
    def visitAddExpressionMult(self, ctx:FeelExprParser.AddExpressionMultContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#addExpression.
    def visitAddExpression(self, ctx:FeelExprParser.AddExpressionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#multExpressionPow.
    def visitMultExpressionPow(self, ctx:FeelExprParser.MultExpressionPowContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#multExpression.
    def visitMultExpression(self, ctx:FeelExprParser.MultExpressionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#powExpressionUnary.
    def visitPowExpressionUnary(self, ctx:FeelExprParser.PowExpressionUnaryContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#powExpression.
    def visitPowExpression(self, ctx:FeelExprParser.PowExpressionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#pathDescendantFilterExpression.
    def visitPathDescendantFilterExpression(self, ctx:FeelExprParser.PathDescendantFilterExpressionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#signedUnaryExpressionPlus.
    def visitSignedUnaryExpressionPlus(self, ctx:FeelExprParser.SignedUnaryExpressionPlusContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#signedUnaryExpressionMinus.
    def visitSignedUnaryExpressionMinus(self, ctx:FeelExprParser.SignedUnaryExpressionMinusContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#fnInvocation.
    def visitFnInvocation(self, ctx:FeelExprParser.FnInvocationContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#nonSignedUnaryExpression.
    def visitNonSignedUnaryExpression(self, ctx:FeelExprParser.NonSignedUnaryExpressionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#uenpmPrimary.
    def visitUenpmPrimary(self, ctx:FeelExprParser.UenpmPrimaryContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#primaryLiteral.
    def visitPrimaryLiteral(self, ctx:FeelExprParser.PrimaryLiteralContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#primaryForExpression.
    def visitPrimaryForExpression(self, ctx:FeelExprParser.PrimaryForExpressionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#primaryQuantifiedExpression.
    def visitPrimaryQuantifiedExpression(self, ctx:FeelExprParser.PrimaryQuantifiedExpressionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#primaryIfExpression.
    def visitPrimaryIfExpression(self, ctx:FeelExprParser.PrimaryIfExpressionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#primaryInterval.
    def visitPrimaryInterval(self, ctx:FeelExprParser.PrimaryIntervalContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#primaryList.
    def visitPrimaryList(self, ctx:FeelExprParser.PrimaryListContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#primaryContext.
    def visitPrimaryContext(self, ctx:FeelExprParser.PrimaryContextContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#primaryParens.
    def visitPrimaryParens(self, ctx:FeelExprParser.PrimaryParensContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#primaryUnaryTest.
    def visitPrimaryUnaryTest(self, ctx:FeelExprParser.PrimaryUnaryTestContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#primaryName.
    def visitPrimaryName(self, ctx:FeelExprParser.PrimaryNameContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#numberLiteral.
    def visitNumberLiteral(self, ctx:FeelExprParser.NumberLiteralContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#boolLiteral.
    def visitBoolLiteral(self, ctx:FeelExprParser.BoolLiteralContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#atLiteralLabel.
    def visitAtLiteralLabel(self, ctx:FeelExprParser.AtLiteralLabelContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#stringLiteral.
    def visitStringLiteral(self, ctx:FeelExprParser.StringLiteralContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#nullLiteral.
    def visitNullLiteral(self, ctx:FeelExprParser.NullLiteralContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#undefined.
    def visitUndefined(self, ctx:FeelExprParser.UndefinedContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#atLiteral.
    def visitAtLiteral(self, ctx:FeelExprParser.AtLiteralContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#atLiteralValue.
    def visitAtLiteralValue(self, ctx:FeelExprParser.AtLiteralValueContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#positiveUnaryTestIneqInterval.
    def visitPositiveUnaryTestIneqInterval(self, ctx:FeelExprParser.PositiveUnaryTestIneqIntervalContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#positiveUnaryTestIneq.
    def visitPositiveUnaryTestIneq(self, ctx:FeelExprParser.PositiveUnaryTestIneqContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#positiveUnaryTestInterval.
    def visitPositiveUnaryTestInterval(self, ctx:FeelExprParser.PositiveUnaryTestIntervalContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#simplePositiveUnaryTests.
    def visitSimplePositiveUnaryTests(self, ctx:FeelExprParser.SimplePositiveUnaryTestsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#positiveSimplePositiveUnaryTests.
    def visitPositiveSimplePositiveUnaryTests(self, ctx:FeelExprParser.PositiveSimplePositiveUnaryTestsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#negatedSimplePositiveUnaryTests.
    def visitNegatedSimplePositiveUnaryTests(self, ctx:FeelExprParser.NegatedSimplePositiveUnaryTestsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#positiveUnaryTestDash.
    def visitPositiveUnaryTestDash(self, ctx:FeelExprParser.PositiveUnaryTestDashContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#positiveUnaryTest.
    def visitPositiveUnaryTest(self, ctx:FeelExprParser.PositiveUnaryTestContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#positiveUnaryTests.
    def visitPositiveUnaryTests(self, ctx:FeelExprParser.PositiveUnaryTestsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#unaryTestsRoot.
    def visitUnaryTestsRoot(self, ctx:FeelExprParser.UnaryTestsRootContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#unaryTests_negated.
    def visitUnaryTests_negated(self, ctx:FeelExprParser.UnaryTests_negatedContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#unaryTests_positive.
    def visitUnaryTests_positive(self, ctx:FeelExprParser.UnaryTests_positiveContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#unaryTests_empty.
    def visitUnaryTests_empty(self, ctx:FeelExprParser.UnaryTests_emptyContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#endpoint.
    def visitEndpoint(self, ctx:FeelExprParser.EndpointContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#interval.
    def visitInterval(self, ctx:FeelExprParser.IntervalContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#qualifiedName.
    def visitQualifiedName(self, ctx:FeelExprParser.QualifiedNameContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#nameRef.
    def visitNameRef(self, ctx:FeelExprParser.NameRefContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#nameRefOtherToken.
    def visitNameRefOtherToken(self, ctx:FeelExprParser.NameRefOtherTokenContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by FeelExprParser#reusableKeywords.
    def visitReusableKeywords(self, ctx:FeelExprParser.ReusableKeywordsContext):
        return self.visitChildren(ctx)



del FeelExprParser