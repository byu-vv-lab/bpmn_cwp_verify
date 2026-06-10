# Generated from antlr/FeelExpr.g4 by ANTLR 4.13.2
from antlr4 import *
if "." in __name__:
    from .FeelExprParser import FeelExprParser
else:
    from FeelExprParser import FeelExprParser

# This class defines a complete listener for a parse tree produced by FeelExprParser.
class FeelExprListener(ParseTreeListener):

    # Enter a parse tree produced by FeelExprParser#compilation_unit.
    def enterCompilation_unit(self, ctx:FeelExprParser.Compilation_unitContext):
        pass

    # Exit a parse tree produced by FeelExprParser#compilation_unit.
    def exitCompilation_unit(self, ctx:FeelExprParser.Compilation_unitContext):
        pass


    # Enter a parse tree produced by FeelExprParser#expressionTextual.
    def enterExpressionTextual(self, ctx:FeelExprParser.ExpressionTextualContext):
        pass

    # Exit a parse tree produced by FeelExprParser#expressionTextual.
    def exitExpressionTextual(self, ctx:FeelExprParser.ExpressionTextualContext):
        pass


    # Enter a parse tree produced by FeelExprParser#textualExpression.
    def enterTextualExpression(self, ctx:FeelExprParser.TextualExpressionContext):
        pass

    # Exit a parse tree produced by FeelExprParser#textualExpression.
    def exitTextualExpression(self, ctx:FeelExprParser.TextualExpressionContext):
        pass


    # Enter a parse tree produced by FeelExprParser#parametersEmpty.
    def enterParametersEmpty(self, ctx:FeelExprParser.ParametersEmptyContext):
        pass

    # Exit a parse tree produced by FeelExprParser#parametersEmpty.
    def exitParametersEmpty(self, ctx:FeelExprParser.ParametersEmptyContext):
        pass


    # Enter a parse tree produced by FeelExprParser#parametersNamed.
    def enterParametersNamed(self, ctx:FeelExprParser.ParametersNamedContext):
        pass

    # Exit a parse tree produced by FeelExprParser#parametersNamed.
    def exitParametersNamed(self, ctx:FeelExprParser.ParametersNamedContext):
        pass


    # Enter a parse tree produced by FeelExprParser#parametersPositional.
    def enterParametersPositional(self, ctx:FeelExprParser.ParametersPositionalContext):
        pass

    # Exit a parse tree produced by FeelExprParser#parametersPositional.
    def exitParametersPositional(self, ctx:FeelExprParser.ParametersPositionalContext):
        pass


    # Enter a parse tree produced by FeelExprParser#namedParameters.
    def enterNamedParameters(self, ctx:FeelExprParser.NamedParametersContext):
        pass

    # Exit a parse tree produced by FeelExprParser#namedParameters.
    def exitNamedParameters(self, ctx:FeelExprParser.NamedParametersContext):
        pass


    # Enter a parse tree produced by FeelExprParser#namedParameter.
    def enterNamedParameter(self, ctx:FeelExprParser.NamedParameterContext):
        pass

    # Exit a parse tree produced by FeelExprParser#namedParameter.
    def exitNamedParameter(self, ctx:FeelExprParser.NamedParameterContext):
        pass


    # Enter a parse tree produced by FeelExprParser#positionalParameters.
    def enterPositionalParameters(self, ctx:FeelExprParser.PositionalParametersContext):
        pass

    # Exit a parse tree produced by FeelExprParser#positionalParameters.
    def exitPositionalParameters(self, ctx:FeelExprParser.PositionalParametersContext):
        pass


    # Enter a parse tree produced by FeelExprParser#forExpression.
    def enterForExpression(self, ctx:FeelExprParser.ForExpressionContext):
        pass

    # Exit a parse tree produced by FeelExprParser#forExpression.
    def exitForExpression(self, ctx:FeelExprParser.ForExpressionContext):
        pass


    # Enter a parse tree produced by FeelExprParser#iterationContexts.
    def enterIterationContexts(self, ctx:FeelExprParser.IterationContextsContext):
        pass

    # Exit a parse tree produced by FeelExprParser#iterationContexts.
    def exitIterationContexts(self, ctx:FeelExprParser.IterationContextsContext):
        pass


    # Enter a parse tree produced by FeelExprParser#iterationContext.
    def enterIterationContext(self, ctx:FeelExprParser.IterationContextContext):
        pass

    # Exit a parse tree produced by FeelExprParser#iterationContext.
    def exitIterationContext(self, ctx:FeelExprParser.IterationContextContext):
        pass


    # Enter a parse tree produced by FeelExprParser#ifExpression.
    def enterIfExpression(self, ctx:FeelExprParser.IfExpressionContext):
        pass

    # Exit a parse tree produced by FeelExprParser#ifExpression.
    def exitIfExpression(self, ctx:FeelExprParser.IfExpressionContext):
        pass


    # Enter a parse tree produced by FeelExprParser#quantExprSome.
    def enterQuantExprSome(self, ctx:FeelExprParser.QuantExprSomeContext):
        pass

    # Exit a parse tree produced by FeelExprParser#quantExprSome.
    def exitQuantExprSome(self, ctx:FeelExprParser.QuantExprSomeContext):
        pass


    # Enter a parse tree produced by FeelExprParser#quantExprEvery.
    def enterQuantExprEvery(self, ctx:FeelExprParser.QuantExprEveryContext):
        pass

    # Exit a parse tree produced by FeelExprParser#quantExprEvery.
    def exitQuantExprEvery(self, ctx:FeelExprParser.QuantExprEveryContext):
        pass


    # Enter a parse tree produced by FeelExprParser#listType.
    def enterListType(self, ctx:FeelExprParser.ListTypeContext):
        pass

    # Exit a parse tree produced by FeelExprParser#listType.
    def exitListType(self, ctx:FeelExprParser.ListTypeContext):
        pass


    # Enter a parse tree produced by FeelExprParser#rangeType.
    def enterRangeType(self, ctx:FeelExprParser.RangeTypeContext):
        pass

    # Exit a parse tree produced by FeelExprParser#rangeType.
    def exitRangeType(self, ctx:FeelExprParser.RangeTypeContext):
        pass


    # Enter a parse tree produced by FeelExprParser#contextType.
    def enterContextType(self, ctx:FeelExprParser.ContextTypeContext):
        pass

    # Exit a parse tree produced by FeelExprParser#contextType.
    def exitContextType(self, ctx:FeelExprParser.ContextTypeContext):
        pass


    # Enter a parse tree produced by FeelExprParser#qnType.
    def enterQnType(self, ctx:FeelExprParser.QnTypeContext):
        pass

    # Exit a parse tree produced by FeelExprParser#qnType.
    def exitQnType(self, ctx:FeelExprParser.QnTypeContext):
        pass


    # Enter a parse tree produced by FeelExprParser#functionType.
    def enterFunctionType(self, ctx:FeelExprParser.FunctionTypeContext):
        pass

    # Exit a parse tree produced by FeelExprParser#functionType.
    def exitFunctionType(self, ctx:FeelExprParser.FunctionTypeContext):
        pass


    # Enter a parse tree produced by FeelExprParser#list.
    def enterList(self, ctx:FeelExprParser.ListContext):
        pass

    # Exit a parse tree produced by FeelExprParser#list.
    def exitList(self, ctx:FeelExprParser.ListContext):
        pass


    # Enter a parse tree produced by FeelExprParser#functionDefinition.
    def enterFunctionDefinition(self, ctx:FeelExprParser.FunctionDefinitionContext):
        pass

    # Exit a parse tree produced by FeelExprParser#functionDefinition.
    def exitFunctionDefinition(self, ctx:FeelExprParser.FunctionDefinitionContext):
        pass


    # Enter a parse tree produced by FeelExprParser#formalParameters.
    def enterFormalParameters(self, ctx:FeelExprParser.FormalParametersContext):
        pass

    # Exit a parse tree produced by FeelExprParser#formalParameters.
    def exitFormalParameters(self, ctx:FeelExprParser.FormalParametersContext):
        pass


    # Enter a parse tree produced by FeelExprParser#formalParameter.
    def enterFormalParameter(self, ctx:FeelExprParser.FormalParameterContext):
        pass

    # Exit a parse tree produced by FeelExprParser#formalParameter.
    def exitFormalParameter(self, ctx:FeelExprParser.FormalParameterContext):
        pass


    # Enter a parse tree produced by FeelExprParser#context.
    def enterContext(self, ctx:FeelExprParser.ContextContext):
        pass

    # Exit a parse tree produced by FeelExprParser#context.
    def exitContext(self, ctx:FeelExprParser.ContextContext):
        pass


    # Enter a parse tree produced by FeelExprParser#contextEntries.
    def enterContextEntries(self, ctx:FeelExprParser.ContextEntriesContext):
        pass

    # Exit a parse tree produced by FeelExprParser#contextEntries.
    def exitContextEntries(self, ctx:FeelExprParser.ContextEntriesContext):
        pass


    # Enter a parse tree produced by FeelExprParser#contextEntry.
    def enterContextEntry(self, ctx:FeelExprParser.ContextEntryContext):
        pass

    # Exit a parse tree produced by FeelExprParser#contextEntry.
    def exitContextEntry(self, ctx:FeelExprParser.ContextEntryContext):
        pass


    # Enter a parse tree produced by FeelExprParser#keyName.
    def enterKeyName(self, ctx:FeelExprParser.KeyNameContext):
        pass

    # Exit a parse tree produced by FeelExprParser#keyName.
    def exitKeyName(self, ctx:FeelExprParser.KeyNameContext):
        pass


    # Enter a parse tree produced by FeelExprParser#keyString.
    def enterKeyString(self, ctx:FeelExprParser.KeyStringContext):
        pass

    # Exit a parse tree produced by FeelExprParser#keyString.
    def exitKeyString(self, ctx:FeelExprParser.KeyStringContext):
        pass


    # Enter a parse tree produced by FeelExprParser#nameDefinition.
    def enterNameDefinition(self, ctx:FeelExprParser.NameDefinitionContext):
        pass

    # Exit a parse tree produced by FeelExprParser#nameDefinition.
    def exitNameDefinition(self, ctx:FeelExprParser.NameDefinitionContext):
        pass


    # Enter a parse tree produced by FeelExprParser#nameDefinitionWithEOF.
    def enterNameDefinitionWithEOF(self, ctx:FeelExprParser.NameDefinitionWithEOFContext):
        pass

    # Exit a parse tree produced by FeelExprParser#nameDefinitionWithEOF.
    def exitNameDefinitionWithEOF(self, ctx:FeelExprParser.NameDefinitionWithEOFContext):
        pass


    # Enter a parse tree produced by FeelExprParser#nameDefinitionTokens.
    def enterNameDefinitionTokens(self, ctx:FeelExprParser.NameDefinitionTokensContext):
        pass

    # Exit a parse tree produced by FeelExprParser#nameDefinitionTokens.
    def exitNameDefinitionTokens(self, ctx:FeelExprParser.NameDefinitionTokensContext):
        pass


    # Enter a parse tree produced by FeelExprParser#iterationNameDefinition.
    def enterIterationNameDefinition(self, ctx:FeelExprParser.IterationNameDefinitionContext):
        pass

    # Exit a parse tree produced by FeelExprParser#iterationNameDefinition.
    def exitIterationNameDefinition(self, ctx:FeelExprParser.IterationNameDefinitionContext):
        pass


    # Enter a parse tree produced by FeelExprParser#iterationNameDefinitionTokens.
    def enterIterationNameDefinitionTokens(self, ctx:FeelExprParser.IterationNameDefinitionTokensContext):
        pass

    # Exit a parse tree produced by FeelExprParser#iterationNameDefinitionTokens.
    def exitIterationNameDefinitionTokens(self, ctx:FeelExprParser.IterationNameDefinitionTokensContext):
        pass


    # Enter a parse tree produced by FeelExprParser#additionalNameSymbol.
    def enterAdditionalNameSymbol(self, ctx:FeelExprParser.AdditionalNameSymbolContext):
        pass

    # Exit a parse tree produced by FeelExprParser#additionalNameSymbol.
    def exitAdditionalNameSymbol(self, ctx:FeelExprParser.AdditionalNameSymbolContext):
        pass


    # Enter a parse tree produced by FeelExprParser#condOr.
    def enterCondOr(self, ctx:FeelExprParser.CondOrContext):
        pass

    # Exit a parse tree produced by FeelExprParser#condOr.
    def exitCondOr(self, ctx:FeelExprParser.CondOrContext):
        pass


    # Enter a parse tree produced by FeelExprParser#condOrAnd.
    def enterCondOrAnd(self, ctx:FeelExprParser.CondOrAndContext):
        pass

    # Exit a parse tree produced by FeelExprParser#condOrAnd.
    def exitCondOrAnd(self, ctx:FeelExprParser.CondOrAndContext):
        pass


    # Enter a parse tree produced by FeelExprParser#condAndComp.
    def enterCondAndComp(self, ctx:FeelExprParser.CondAndCompContext):
        pass

    # Exit a parse tree produced by FeelExprParser#condAndComp.
    def exitCondAndComp(self, ctx:FeelExprParser.CondAndCompContext):
        pass


    # Enter a parse tree produced by FeelExprParser#condAnd.
    def enterCondAnd(self, ctx:FeelExprParser.CondAndContext):
        pass

    # Exit a parse tree produced by FeelExprParser#condAnd.
    def exitCondAnd(self, ctx:FeelExprParser.CondAndContext):
        pass


    # Enter a parse tree produced by FeelExprParser#compExpression.
    def enterCompExpression(self, ctx:FeelExprParser.CompExpressionContext):
        pass

    # Exit a parse tree produced by FeelExprParser#compExpression.
    def exitCompExpression(self, ctx:FeelExprParser.CompExpressionContext):
        pass


    # Enter a parse tree produced by FeelExprParser#compExpressionRel.
    def enterCompExpressionRel(self, ctx:FeelExprParser.CompExpressionRelContext):
        pass

    # Exit a parse tree produced by FeelExprParser#compExpressionRel.
    def exitCompExpressionRel(self, ctx:FeelExprParser.CompExpressionRelContext):
        pass


    # Enter a parse tree produced by FeelExprParser#relExpressionBetween.
    def enterRelExpressionBetween(self, ctx:FeelExprParser.RelExpressionBetweenContext):
        pass

    # Exit a parse tree produced by FeelExprParser#relExpressionBetween.
    def exitRelExpressionBetween(self, ctx:FeelExprParser.RelExpressionBetweenContext):
        pass


    # Enter a parse tree produced by FeelExprParser#relExpressionValue.
    def enterRelExpressionValue(self, ctx:FeelExprParser.RelExpressionValueContext):
        pass

    # Exit a parse tree produced by FeelExprParser#relExpressionValue.
    def exitRelExpressionValue(self, ctx:FeelExprParser.RelExpressionValueContext):
        pass


    # Enter a parse tree produced by FeelExprParser#relExpressionTestList.
    def enterRelExpressionTestList(self, ctx:FeelExprParser.RelExpressionTestListContext):
        pass

    # Exit a parse tree produced by FeelExprParser#relExpressionTestList.
    def exitRelExpressionTestList(self, ctx:FeelExprParser.RelExpressionTestListContext):
        pass


    # Enter a parse tree produced by FeelExprParser#relExpressionAdd.
    def enterRelExpressionAdd(self, ctx:FeelExprParser.RelExpressionAddContext):
        pass

    # Exit a parse tree produced by FeelExprParser#relExpressionAdd.
    def exitRelExpressionAdd(self, ctx:FeelExprParser.RelExpressionAddContext):
        pass


    # Enter a parse tree produced by FeelExprParser#relExpressionInstanceOf.
    def enterRelExpressionInstanceOf(self, ctx:FeelExprParser.RelExpressionInstanceOfContext):
        pass

    # Exit a parse tree produced by FeelExprParser#relExpressionInstanceOf.
    def exitRelExpressionInstanceOf(self, ctx:FeelExprParser.RelExpressionInstanceOfContext):
        pass


    # Enter a parse tree produced by FeelExprParser#expressionList.
    def enterExpressionList(self, ctx:FeelExprParser.ExpressionListContext):
        pass

    # Exit a parse tree produced by FeelExprParser#expressionList.
    def exitExpressionList(self, ctx:FeelExprParser.ExpressionListContext):
        pass


    # Enter a parse tree produced by FeelExprParser#addExpressionMult.
    def enterAddExpressionMult(self, ctx:FeelExprParser.AddExpressionMultContext):
        pass

    # Exit a parse tree produced by FeelExprParser#addExpressionMult.
    def exitAddExpressionMult(self, ctx:FeelExprParser.AddExpressionMultContext):
        pass


    # Enter a parse tree produced by FeelExprParser#addExpression.
    def enterAddExpression(self, ctx:FeelExprParser.AddExpressionContext):
        pass

    # Exit a parse tree produced by FeelExprParser#addExpression.
    def exitAddExpression(self, ctx:FeelExprParser.AddExpressionContext):
        pass


    # Enter a parse tree produced by FeelExprParser#multExpressionPow.
    def enterMultExpressionPow(self, ctx:FeelExprParser.MultExpressionPowContext):
        pass

    # Exit a parse tree produced by FeelExprParser#multExpressionPow.
    def exitMultExpressionPow(self, ctx:FeelExprParser.MultExpressionPowContext):
        pass


    # Enter a parse tree produced by FeelExprParser#multExpression.
    def enterMultExpression(self, ctx:FeelExprParser.MultExpressionContext):
        pass

    # Exit a parse tree produced by FeelExprParser#multExpression.
    def exitMultExpression(self, ctx:FeelExprParser.MultExpressionContext):
        pass


    # Enter a parse tree produced by FeelExprParser#powExpressionUnary.
    def enterPowExpressionUnary(self, ctx:FeelExprParser.PowExpressionUnaryContext):
        pass

    # Exit a parse tree produced by FeelExprParser#powExpressionUnary.
    def exitPowExpressionUnary(self, ctx:FeelExprParser.PowExpressionUnaryContext):
        pass


    # Enter a parse tree produced by FeelExprParser#powExpression.
    def enterPowExpression(self, ctx:FeelExprParser.PowExpressionContext):
        pass

    # Exit a parse tree produced by FeelExprParser#powExpression.
    def exitPowExpression(self, ctx:FeelExprParser.PowExpressionContext):
        pass


    # Enter a parse tree produced by FeelExprParser#pathDescendantFilterExpression.
    def enterPathDescendantFilterExpression(self, ctx:FeelExprParser.PathDescendantFilterExpressionContext):
        pass

    # Exit a parse tree produced by FeelExprParser#pathDescendantFilterExpression.
    def exitPathDescendantFilterExpression(self, ctx:FeelExprParser.PathDescendantFilterExpressionContext):
        pass


    # Enter a parse tree produced by FeelExprParser#signedUnaryExpressionPlus.
    def enterSignedUnaryExpressionPlus(self, ctx:FeelExprParser.SignedUnaryExpressionPlusContext):
        pass

    # Exit a parse tree produced by FeelExprParser#signedUnaryExpressionPlus.
    def exitSignedUnaryExpressionPlus(self, ctx:FeelExprParser.SignedUnaryExpressionPlusContext):
        pass


    # Enter a parse tree produced by FeelExprParser#signedUnaryExpressionMinus.
    def enterSignedUnaryExpressionMinus(self, ctx:FeelExprParser.SignedUnaryExpressionMinusContext):
        pass

    # Exit a parse tree produced by FeelExprParser#signedUnaryExpressionMinus.
    def exitSignedUnaryExpressionMinus(self, ctx:FeelExprParser.SignedUnaryExpressionMinusContext):
        pass


    # Enter a parse tree produced by FeelExprParser#fnInvocation.
    def enterFnInvocation(self, ctx:FeelExprParser.FnInvocationContext):
        pass

    # Exit a parse tree produced by FeelExprParser#fnInvocation.
    def exitFnInvocation(self, ctx:FeelExprParser.FnInvocationContext):
        pass


    # Enter a parse tree produced by FeelExprParser#nonSignedUnaryExpression.
    def enterNonSignedUnaryExpression(self, ctx:FeelExprParser.NonSignedUnaryExpressionContext):
        pass

    # Exit a parse tree produced by FeelExprParser#nonSignedUnaryExpression.
    def exitNonSignedUnaryExpression(self, ctx:FeelExprParser.NonSignedUnaryExpressionContext):
        pass


    # Enter a parse tree produced by FeelExprParser#uenpmPrimary.
    def enterUenpmPrimary(self, ctx:FeelExprParser.UenpmPrimaryContext):
        pass

    # Exit a parse tree produced by FeelExprParser#uenpmPrimary.
    def exitUenpmPrimary(self, ctx:FeelExprParser.UenpmPrimaryContext):
        pass


    # Enter a parse tree produced by FeelExprParser#primaryLiteral.
    def enterPrimaryLiteral(self, ctx:FeelExprParser.PrimaryLiteralContext):
        pass

    # Exit a parse tree produced by FeelExprParser#primaryLiteral.
    def exitPrimaryLiteral(self, ctx:FeelExprParser.PrimaryLiteralContext):
        pass


    # Enter a parse tree produced by FeelExprParser#primaryForExpression.
    def enterPrimaryForExpression(self, ctx:FeelExprParser.PrimaryForExpressionContext):
        pass

    # Exit a parse tree produced by FeelExprParser#primaryForExpression.
    def exitPrimaryForExpression(self, ctx:FeelExprParser.PrimaryForExpressionContext):
        pass


    # Enter a parse tree produced by FeelExprParser#primaryQuantifiedExpression.
    def enterPrimaryQuantifiedExpression(self, ctx:FeelExprParser.PrimaryQuantifiedExpressionContext):
        pass

    # Exit a parse tree produced by FeelExprParser#primaryQuantifiedExpression.
    def exitPrimaryQuantifiedExpression(self, ctx:FeelExprParser.PrimaryQuantifiedExpressionContext):
        pass


    # Enter a parse tree produced by FeelExprParser#primaryIfExpression.
    def enterPrimaryIfExpression(self, ctx:FeelExprParser.PrimaryIfExpressionContext):
        pass

    # Exit a parse tree produced by FeelExprParser#primaryIfExpression.
    def exitPrimaryIfExpression(self, ctx:FeelExprParser.PrimaryIfExpressionContext):
        pass


    # Enter a parse tree produced by FeelExprParser#primaryInterval.
    def enterPrimaryInterval(self, ctx:FeelExprParser.PrimaryIntervalContext):
        pass

    # Exit a parse tree produced by FeelExprParser#primaryInterval.
    def exitPrimaryInterval(self, ctx:FeelExprParser.PrimaryIntervalContext):
        pass


    # Enter a parse tree produced by FeelExprParser#primaryList.
    def enterPrimaryList(self, ctx:FeelExprParser.PrimaryListContext):
        pass

    # Exit a parse tree produced by FeelExprParser#primaryList.
    def exitPrimaryList(self, ctx:FeelExprParser.PrimaryListContext):
        pass


    # Enter a parse tree produced by FeelExprParser#primaryContext.
    def enterPrimaryContext(self, ctx:FeelExprParser.PrimaryContextContext):
        pass

    # Exit a parse tree produced by FeelExprParser#primaryContext.
    def exitPrimaryContext(self, ctx:FeelExprParser.PrimaryContextContext):
        pass


    # Enter a parse tree produced by FeelExprParser#primaryParens.
    def enterPrimaryParens(self, ctx:FeelExprParser.PrimaryParensContext):
        pass

    # Exit a parse tree produced by FeelExprParser#primaryParens.
    def exitPrimaryParens(self, ctx:FeelExprParser.PrimaryParensContext):
        pass


    # Enter a parse tree produced by FeelExprParser#primaryUnaryTest.
    def enterPrimaryUnaryTest(self, ctx:FeelExprParser.PrimaryUnaryTestContext):
        pass

    # Exit a parse tree produced by FeelExprParser#primaryUnaryTest.
    def exitPrimaryUnaryTest(self, ctx:FeelExprParser.PrimaryUnaryTestContext):
        pass


    # Enter a parse tree produced by FeelExprParser#primaryName.
    def enterPrimaryName(self, ctx:FeelExprParser.PrimaryNameContext):
        pass

    # Exit a parse tree produced by FeelExprParser#primaryName.
    def exitPrimaryName(self, ctx:FeelExprParser.PrimaryNameContext):
        pass


    # Enter a parse tree produced by FeelExprParser#numberLiteral.
    def enterNumberLiteral(self, ctx:FeelExprParser.NumberLiteralContext):
        pass

    # Exit a parse tree produced by FeelExprParser#numberLiteral.
    def exitNumberLiteral(self, ctx:FeelExprParser.NumberLiteralContext):
        pass


    # Enter a parse tree produced by FeelExprParser#boolLiteral.
    def enterBoolLiteral(self, ctx:FeelExprParser.BoolLiteralContext):
        pass

    # Exit a parse tree produced by FeelExprParser#boolLiteral.
    def exitBoolLiteral(self, ctx:FeelExprParser.BoolLiteralContext):
        pass


    # Enter a parse tree produced by FeelExprParser#atLiteralLabel.
    def enterAtLiteralLabel(self, ctx:FeelExprParser.AtLiteralLabelContext):
        pass

    # Exit a parse tree produced by FeelExprParser#atLiteralLabel.
    def exitAtLiteralLabel(self, ctx:FeelExprParser.AtLiteralLabelContext):
        pass


    # Enter a parse tree produced by FeelExprParser#stringLiteral.
    def enterStringLiteral(self, ctx:FeelExprParser.StringLiteralContext):
        pass

    # Exit a parse tree produced by FeelExprParser#stringLiteral.
    def exitStringLiteral(self, ctx:FeelExprParser.StringLiteralContext):
        pass


    # Enter a parse tree produced by FeelExprParser#nullLiteral.
    def enterNullLiteral(self, ctx:FeelExprParser.NullLiteralContext):
        pass

    # Exit a parse tree produced by FeelExprParser#nullLiteral.
    def exitNullLiteral(self, ctx:FeelExprParser.NullLiteralContext):
        pass


    # Enter a parse tree produced by FeelExprParser#undefined.
    def enterUndefined(self, ctx:FeelExprParser.UndefinedContext):
        pass

    # Exit a parse tree produced by FeelExprParser#undefined.
    def exitUndefined(self, ctx:FeelExprParser.UndefinedContext):
        pass


    # Enter a parse tree produced by FeelExprParser#atLiteral.
    def enterAtLiteral(self, ctx:FeelExprParser.AtLiteralContext):
        pass

    # Exit a parse tree produced by FeelExprParser#atLiteral.
    def exitAtLiteral(self, ctx:FeelExprParser.AtLiteralContext):
        pass


    # Enter a parse tree produced by FeelExprParser#atLiteralValue.
    def enterAtLiteralValue(self, ctx:FeelExprParser.AtLiteralValueContext):
        pass

    # Exit a parse tree produced by FeelExprParser#atLiteralValue.
    def exitAtLiteralValue(self, ctx:FeelExprParser.AtLiteralValueContext):
        pass


    # Enter a parse tree produced by FeelExprParser#positiveUnaryTestIneqInterval.
    def enterPositiveUnaryTestIneqInterval(self, ctx:FeelExprParser.PositiveUnaryTestIneqIntervalContext):
        pass

    # Exit a parse tree produced by FeelExprParser#positiveUnaryTestIneqInterval.
    def exitPositiveUnaryTestIneqInterval(self, ctx:FeelExprParser.PositiveUnaryTestIneqIntervalContext):
        pass


    # Enter a parse tree produced by FeelExprParser#positiveUnaryTestIneq.
    def enterPositiveUnaryTestIneq(self, ctx:FeelExprParser.PositiveUnaryTestIneqContext):
        pass

    # Exit a parse tree produced by FeelExprParser#positiveUnaryTestIneq.
    def exitPositiveUnaryTestIneq(self, ctx:FeelExprParser.PositiveUnaryTestIneqContext):
        pass


    # Enter a parse tree produced by FeelExprParser#positiveUnaryTestInterval.
    def enterPositiveUnaryTestInterval(self, ctx:FeelExprParser.PositiveUnaryTestIntervalContext):
        pass

    # Exit a parse tree produced by FeelExprParser#positiveUnaryTestInterval.
    def exitPositiveUnaryTestInterval(self, ctx:FeelExprParser.PositiveUnaryTestIntervalContext):
        pass


    # Enter a parse tree produced by FeelExprParser#simplePositiveUnaryTests.
    def enterSimplePositiveUnaryTests(self, ctx:FeelExprParser.SimplePositiveUnaryTestsContext):
        pass

    # Exit a parse tree produced by FeelExprParser#simplePositiveUnaryTests.
    def exitSimplePositiveUnaryTests(self, ctx:FeelExprParser.SimplePositiveUnaryTestsContext):
        pass


    # Enter a parse tree produced by FeelExprParser#positiveSimplePositiveUnaryTests.
    def enterPositiveSimplePositiveUnaryTests(self, ctx:FeelExprParser.PositiveSimplePositiveUnaryTestsContext):
        pass

    # Exit a parse tree produced by FeelExprParser#positiveSimplePositiveUnaryTests.
    def exitPositiveSimplePositiveUnaryTests(self, ctx:FeelExprParser.PositiveSimplePositiveUnaryTestsContext):
        pass


    # Enter a parse tree produced by FeelExprParser#negatedSimplePositiveUnaryTests.
    def enterNegatedSimplePositiveUnaryTests(self, ctx:FeelExprParser.NegatedSimplePositiveUnaryTestsContext):
        pass

    # Exit a parse tree produced by FeelExprParser#negatedSimplePositiveUnaryTests.
    def exitNegatedSimplePositiveUnaryTests(self, ctx:FeelExprParser.NegatedSimplePositiveUnaryTestsContext):
        pass


    # Enter a parse tree produced by FeelExprParser#positiveUnaryTestDash.
    def enterPositiveUnaryTestDash(self, ctx:FeelExprParser.PositiveUnaryTestDashContext):
        pass

    # Exit a parse tree produced by FeelExprParser#positiveUnaryTestDash.
    def exitPositiveUnaryTestDash(self, ctx:FeelExprParser.PositiveUnaryTestDashContext):
        pass


    # Enter a parse tree produced by FeelExprParser#positiveUnaryTest.
    def enterPositiveUnaryTest(self, ctx:FeelExprParser.PositiveUnaryTestContext):
        pass

    # Exit a parse tree produced by FeelExprParser#positiveUnaryTest.
    def exitPositiveUnaryTest(self, ctx:FeelExprParser.PositiveUnaryTestContext):
        pass


    # Enter a parse tree produced by FeelExprParser#positiveUnaryTests.
    def enterPositiveUnaryTests(self, ctx:FeelExprParser.PositiveUnaryTestsContext):
        pass

    # Exit a parse tree produced by FeelExprParser#positiveUnaryTests.
    def exitPositiveUnaryTests(self, ctx:FeelExprParser.PositiveUnaryTestsContext):
        pass


    # Enter a parse tree produced by FeelExprParser#unaryTestsRoot.
    def enterUnaryTestsRoot(self, ctx:FeelExprParser.UnaryTestsRootContext):
        pass

    # Exit a parse tree produced by FeelExprParser#unaryTestsRoot.
    def exitUnaryTestsRoot(self, ctx:FeelExprParser.UnaryTestsRootContext):
        pass


    # Enter a parse tree produced by FeelExprParser#unaryTests_negated.
    def enterUnaryTests_negated(self, ctx:FeelExprParser.UnaryTests_negatedContext):
        pass

    # Exit a parse tree produced by FeelExprParser#unaryTests_negated.
    def exitUnaryTests_negated(self, ctx:FeelExprParser.UnaryTests_negatedContext):
        pass


    # Enter a parse tree produced by FeelExprParser#unaryTests_positive.
    def enterUnaryTests_positive(self, ctx:FeelExprParser.UnaryTests_positiveContext):
        pass

    # Exit a parse tree produced by FeelExprParser#unaryTests_positive.
    def exitUnaryTests_positive(self, ctx:FeelExprParser.UnaryTests_positiveContext):
        pass


    # Enter a parse tree produced by FeelExprParser#unaryTests_empty.
    def enterUnaryTests_empty(self, ctx:FeelExprParser.UnaryTests_emptyContext):
        pass

    # Exit a parse tree produced by FeelExprParser#unaryTests_empty.
    def exitUnaryTests_empty(self, ctx:FeelExprParser.UnaryTests_emptyContext):
        pass


    # Enter a parse tree produced by FeelExprParser#endpoint.
    def enterEndpoint(self, ctx:FeelExprParser.EndpointContext):
        pass

    # Exit a parse tree produced by FeelExprParser#endpoint.
    def exitEndpoint(self, ctx:FeelExprParser.EndpointContext):
        pass


    # Enter a parse tree produced by FeelExprParser#interval.
    def enterInterval(self, ctx:FeelExprParser.IntervalContext):
        pass

    # Exit a parse tree produced by FeelExprParser#interval.
    def exitInterval(self, ctx:FeelExprParser.IntervalContext):
        pass


    # Enter a parse tree produced by FeelExprParser#qualifiedName.
    def enterQualifiedName(self, ctx:FeelExprParser.QualifiedNameContext):
        pass

    # Exit a parse tree produced by FeelExprParser#qualifiedName.
    def exitQualifiedName(self, ctx:FeelExprParser.QualifiedNameContext):
        pass


    # Enter a parse tree produced by FeelExprParser#nameRef.
    def enterNameRef(self, ctx:FeelExprParser.NameRefContext):
        pass

    # Exit a parse tree produced by FeelExprParser#nameRef.
    def exitNameRef(self, ctx:FeelExprParser.NameRefContext):
        pass


    # Enter a parse tree produced by FeelExprParser#nameRefOtherToken.
    def enterNameRefOtherToken(self, ctx:FeelExprParser.NameRefOtherTokenContext):
        pass

    # Exit a parse tree produced by FeelExprParser#nameRefOtherToken.
    def exitNameRefOtherToken(self, ctx:FeelExprParser.NameRefOtherTokenContext):
        pass


    # Enter a parse tree produced by FeelExprParser#reusableKeywords.
    def enterReusableKeywords(self, ctx:FeelExprParser.ReusableKeywordsContext):
        pass

    # Exit a parse tree produced by FeelExprParser#reusableKeywords.
    def exitReusableKeywords(self, ctx:FeelExprParser.ReusableKeywordsContext):
        pass



del FeelExprParser