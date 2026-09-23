# Generated from antlr/StateMmd.g4 by ANTLR 4.13.2
from antlr4 import *
if "." in __name__:
    from .StateMmdParser import StateMmdParser
else:
    from StateMmdParser import StateMmdParser

# This class defines a complete listener for a parse tree produced by StateMmdParser.
class StateMmdListener(ParseTreeListener):

    # Enter a parse tree produced by StateMmdParser#stateFile.
    def enterStateFile(self, ctx:StateMmdParser.StateFileContext):
        pass

    # Exit a parse tree produced by StateMmdParser#stateFile.
    def exitStateFile(self, ctx:StateMmdParser.StateFileContext):
        pass


    # Enter a parse tree produced by StateMmdParser#element.
    def enterElement(self, ctx:StateMmdParser.ElementContext):
        pass

    # Exit a parse tree produced by StateMmdParser#element.
    def exitElement(self, ctx:StateMmdParser.ElementContext):
        pass


    # Enter a parse tree produced by StateMmdParser#enum_type_decl.
    def enterEnum_type_decl(self, ctx:StateMmdParser.Enum_type_declContext):
        pass

    # Exit a parse tree produced by StateMmdParser#enum_type_decl.
    def exitEnum_type_decl(self, ctx:StateMmdParser.Enum_type_declContext):
        pass


    # Enter a parse tree produced by StateMmdParser#id_set.
    def enterId_set(self, ctx:StateMmdParser.Id_setContext):
        pass

    # Exit a parse tree produced by StateMmdParser#id_set.
    def exitId_set(self, ctx:StateMmdParser.Id_setContext):
        pass


    # Enter a parse tree produced by StateMmdParser#const_var_decl.
    def enterConst_var_decl(self, ctx:StateMmdParser.Const_var_declContext):
        pass

    # Exit a parse tree produced by StateMmdParser#const_var_decl.
    def exitConst_var_decl(self, ctx:StateMmdParser.Const_var_declContext):
        pass


    # Enter a parse tree produced by StateMmdParser#var_decl.
    def enterVar_decl(self, ctx:StateMmdParser.Var_declContext):
        pass

    # Exit a parse tree produced by StateMmdParser#var_decl.
    def exitVar_decl(self, ctx:StateMmdParser.Var_declContext):
        pass


    # Enter a parse tree produced by StateMmdParser#array_decl.
    def enterArray_decl(self, ctx:StateMmdParser.Array_declContext):
        pass

    # Exit a parse tree produced by StateMmdParser#array_decl.
    def exitArray_decl(self, ctx:StateMmdParser.Array_declContext):
        pass


    # Enter a parse tree produced by StateMmdParser#type.
    def enterType(self, ctx:StateMmdParser.TypeContext):
        pass

    # Exit a parse tree produced by StateMmdParser#type.
    def exitType(self, ctx:StateMmdParser.TypeContext):
        pass


    # Enter a parse tree produced by StateMmdParser#primitive_type.
    def enterPrimitive_type(self, ctx:StateMmdParser.Primitive_typeContext):
        pass

    # Exit a parse tree produced by StateMmdParser#primitive_type.
    def exitPrimitive_type(self, ctx:StateMmdParser.Primitive_typeContext):
        pass


    # Enter a parse tree produced by StateMmdParser#relationship.
    def enterRelationship(self, ctx:StateMmdParser.RelationshipContext):
        pass

    # Exit a parse tree produced by StateMmdParser#relationship.
    def exitRelationship(self, ctx:StateMmdParser.RelationshipContext):
        pass


    # Enter a parse tree produced by StateMmdParser#ignored_class_decl.
    def enterIgnored_class_decl(self, ctx:StateMmdParser.Ignored_class_declContext):
        pass

    # Exit a parse tree produced by StateMmdParser#ignored_class_decl.
    def exitIgnored_class_decl(self, ctx:StateMmdParser.Ignored_class_declContext):
        pass


    # Enter a parse tree produced by StateMmdParser#generic_text.
    def enterGeneric_text(self, ctx:StateMmdParser.Generic_textContext):
        pass

    # Exit a parse tree produced by StateMmdParser#generic_text.
    def exitGeneric_text(self, ctx:StateMmdParser.Generic_textContext):
        pass



del StateMmdParser