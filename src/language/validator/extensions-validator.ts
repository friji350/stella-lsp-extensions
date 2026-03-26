/**
 * @module Validates that the required extensions for a given syntax are enabled.
 * Based on https://github.com/fizruk/stella/blob/main/stella/src/Language/Stella/ExtensionCheck.hs
 */

import {
  isAstNode,
  type AstNode,
  type CstNode,
  type ValidationAcceptor,
  type ValidationChecks,
} from "langium";
import type {
  Tuple,
  DotRecord,
  List,
  ConsList,
  Variant,
  Let,
  LetRec,
  Sequence,
  ConstInt,
  Ref,
  Throw,
  TryCatch,
  Panic,
  DeclExceptionType,
  DeclExceptionVariant,
  PatternTuple,
  PatternList,
  PatternRecord,
  PatternVariant,
  PatternCons,
  PatternInl,
  PatternInr,
  Program,
  Record,
  StellaAstType,
  DeclFunGeneric,
  DeclFun,
  ConstUnit,
  Application,
  TypeAsc,
  Inl,
  Inr,
  Add,
  Subtraction,
  Multiply,
  Divide,
  Head,
  IsEmpty,
  Tail,
  Pred,
  Fix,
  Fold,
  Unfold,
  DotTuple,
  LogicOr,
  LogicAnd,
  LogicNot,
  LessThan,
  LessThanOrEqual,
  GreaterThan,
  GreaterThanOrEqual,
  Equal,
  NotEqual,
  Assign,
  Deref,
  ConstMemory,
  TypeCast,
  TryWith,
  TryCastAs,
  TypeAbstraction,
  TypeApplication,
  PatternAsc,
  PatternCastAs,
  Pattern,
  PatternInt,
  InlineAnnotation,
  TypeAuto,
  TypeFun,
  TypeRec,
  TypeSum,
  TypeTuple,
  TypeRecord,
  TypeVariant,
  TypeList,
  TypeUnit,
  TypeVar,
  TypeTop,
  TypeBottom,
  TypeRef,
  TypeForAll,
} from "../generated/ast.js";
import {
  isDeclTypeAlias,
  isDeclExceptionType,
  isDeclExceptionVariant,
  isPatternVar,
} from "../generated/ast.js";
import type { StellaServices } from "../stella-module.js";
import { getExtensions, Extensions } from "../extensions.js";
import { DiagnosticCodes } from "./errors.js";

export function registerExtensionChecks(services: StellaServices) {
  const registry = services.validation.ValidationRegistry;
  const validator = services.validation.ExtensionValidator;
  const checks: ValidationChecks<StellaAstType> = {
    // Declarations
    DeclFun: [
      validator.checkLocalDeclarations,
      validator.checkParamsCount,
      validator.checkReturnType,
      validator.checkThrowType,
    ],
    DeclFunGeneric: [
      validator.checkDeclFunGeneric,
      validator.checkLocalDeclarations,
      validator.checkParamsCount,
      validator.checkReturnType,
      validator.checkThrowType,
    ],
    InlineAnnotation: validator.checkAnnotations,
    DeclExceptionType: validator.checkExceptionTypeDeclaration,
    DeclExceptionVariant: validator.checkExceptionVariantDeclaration,

    // Expressions
    ConstUnit: validator.checkConstUnit,
    ConstInt: validator.checkConstInt,
    Application: validator.checkApplication,
    Sequence: validator.checkSequence,
    Let: validator.checkLetBindings,
    LetRec: validator.checkLetRecBindings,
    TypeAsc: validator.checkTypeAsc,
    Tuple: validator.checkTuple,
    Record: validator.checkRecord,
    DotRecord: validator.checkRecord,
    Inl: validator.checkSumTypes,
    Inr: validator.checkSumTypes,
    Variant: validator.checkVariant,
    Add: validator.checkArithmetic,
    Subtraction: validator.checkArithmetic,
    Multiply: validator.checkArithmetic,
    Divide: validator.checkArithmetic,
    List: validator.checkList,
    ConsList: validator.checkList,
    Head: validator.checkList,
    IsEmpty: validator.checkList,
    Tail: validator.checkList,
    Pred: validator.checkPred,
    Fix: validator.checkFix,
    Fold: validator.checkIsorecursiveTypes,
    Unfold: validator.checkIsorecursiveTypes,
    DotTuple: validator.checkDotTuple,
    LogicOr: validator.checkLogicalOperators,
    LogicAnd: validator.checkLogicalOperators,
    LogicNot: validator.checkLogicalOperators,
    LessThan: validator.checkComparisonOperators,
    LessThanOrEqual: validator.checkComparisonOperators,
    GreaterThan: validator.checkComparisonOperators,
    GreaterThanOrEqual: validator.checkComparisonOperators,
    Equal: validator.checkComparisonOperators,
    NotEqual: validator.checkComparisonOperators,
    Assign: validator.checkReferences,
    Ref: validator.checkReferences,
    Deref: validator.checkReferences,
    ConstMemory: validator.checkReferences,
    TypeCast: validator.checkTypeCast,
    Panic: validator.checkPanic,
    Throw: validator.checkExceptions,
    TryCatch: validator.checkExceptions,
    TryWith: validator.checkExceptions,
    TryCastAs: validator.checkTryCastAs,
    TypeAbstraction: validator.checkUniversalTypes,
    TypeApplication: validator.checkUniversalTypes,

    // Patterns
    PatternAsc: validator.checkPatternAsc,
    PatternCastAs: validator.checkPatternCastAs,
    PatternInl: validator.checkPatternSumTypes,
    PatternInr: validator.checkPatternSumTypes,
    PatternVariant: validator.checkPatternVariant,
    PatternTuple: validator.checkPatternTuple,
    PatternRecord: validator.checkPatternRecord,
    PatternList: validator.checkPatternList,
    PatternCons: validator.checkPatternList,
    PatternTrue: validator.checkStructuralPatterns,
    PatternFalse: validator.checkStructuralPatterns,
    PatternUnit: validator.checkStructuralPatterns,
    PatternInt: validator.checkPatternInt,
    PatternSucc: validator.checkStructuralPatterns,

    // Types
    TypeAuto: validator.checkTypeAuto,
    TypeFun: validator.checkTypeFun,
    TypeRec: validator.checkTypeRec,
    TypeSum: validator.checkTypeSum,
    TypeTuple: validator.checkTypeTuple,
    TypeRecord: validator.checkTypeRecord,
    TypeVariant: validator.checkTypeVariant,
    TypeList: validator.checkTypeList,
    TypeUnit: validator.checkTypeUnit,
    TypeVar: validator.checkTypeVar,
    TypeTop: validator.checkTypeTop,
    TypeBottom: validator.checkTypeBottom,
    TypeRef: validator.checkTypeRef,
    TypeForAll: validator.checkTypeForAll,
  };
  registry.register(checks, validator);
}

const oneOfFormatter = new Intl.ListFormat(undefined, { type: "disjunction" });
const oneOf = (items: string[]) => oneOfFormatter.format(items);

export class StellaExtensionValidator {
  private getProgramFromNode(node: AstNode | CstNode): Program {
    if (isAstNode(node)) {
      return node.$cstNode!.root.astNode as Program;
    }
    return node.root.astNode as Program;
  }

  private hasExtension(
    node: AstNode | CstNode,
    exts: Extensions | Extensions[]
  ): boolean {
    const program = this.getProgramFromNode(node);
    const progExtensions = getExtensions(program);

    if (!Array.isArray(exts)) {
      exts = [exts];
    }

    return exts.some((ext) => progExtensions.has(ext));
  }

  private requireExtension(
    feature: string,
    node: AstNode,
    exts: Extensions | Extensions[],
    accept: ValidationAcceptor
  ) {
    if (this.hasExtension(node, exts)) return;

    if (!Array.isArray(exts)) {
      exts = [exts];
    }

    accept(
      "error",
      `Using ${feature} requires ${exts.length > 1 ? "one of " : ""}the ${oneOf(
        exts
      )} extension${exts.length > 1 ? "s" : ""}`,
      {
        node,
        code: DiagnosticCodes.MISSING_EXTENSION,
        data: {
          extensions: exts,
        },
      }
    );
  }

  // Declarations

  checkDeclFunGeneric(decl: DeclFunGeneric, accept: ValidationAcceptor): void {
    this.requireExtension(
      "generic functions",
      decl,
      Extensions.UniversalTypes,
      accept
    );
  }

  checkExceptionTypeDeclaration(
    node: DeclExceptionType,
    accept: ValidationAcceptor
  ): void {
    this.requireExtension(
      "exception type declaration",
      node,
      Extensions.ExceptionTypeDeclaration,
      accept
    );
  }

  checkExceptionVariantDeclaration(
    node: DeclExceptionVariant,
    accept: ValidationAcceptor
  ): void {
    this.requireExtension(
      "exception variant declaration",
      node,
      Extensions.ExceptionTypeDeclaration,
      accept
    );
  }

  checkLocalDeclarations(
    decl: DeclFun | DeclFunGeneric,
    accept: ValidationAcceptor
  ): void {
    if (decl.localDecls.length === 0) return;

    this.requireExtension(
      "nested declarations in functions",
      decl.localDecls[0],
      Extensions.NestedFunctionDeclarations,
      accept
    );

    decl.localDecls.forEach((decl) => {
      if (isDeclTypeAlias(decl)) {
        accept("error", "Type aliases must be global", { node: decl });
      } else if (isDeclExceptionType(decl)) {
        accept("error", "Exception types must be global", { node: decl });
      } else if (isDeclExceptionVariant(decl)) {
        accept("error", "Exception variants must be global", { node: decl });
      }
    });
  }

  checkAnnotations(
    annotation: InlineAnnotation,
    accept: ValidationAcceptor
  ): void {
    this.requireExtension(
      "inline annotation",
      annotation,
      Extensions.InlineFunctions,
      accept
    );
  }

  checkParamsCount(
    decl: DeclFun | DeclFunGeneric,
    accept: ValidationAcceptor
  ): void {
    if (decl.paramDecls.length < 1) {
      this.requireExtension(
        "nullary functions",
        decl,
        Extensions.NullaryFunctions,
        accept
      );
    } else if (decl.paramDecls.length > 1) {
      this.requireExtension(
        "multi-parameter functions",
        decl,
        Extensions.MultiparameterFunctions,
        accept
      );
    }
  }

  checkReturnType(
    decl: DeclFun | DeclFunGeneric,
    accept: ValidationAcceptor
  ): void {
    if (decl.returnType) return;

    this.requireExtension(
      "functions without a return type",
      decl,
      [Extensions.NoReturnTypeAsAuto, Extensions.NoReturnTypeAsUnit],
      accept
    );
  }

  checkThrowType(
    decl: DeclFun | DeclFunGeneric,
    accept: ValidationAcceptor
  ): void {
    if (decl.throwTypes.length === 0) return;

    this.requireExtension(
      "throw type annotations",
      decl.throwTypes[0],
      Extensions.ThrowTypeAnnotations,
      accept
    );
  }

  // Patterns

  checkStructuralPatterns(pattern: Pattern, accept: ValidationAcceptor): void {
    this.requireExtension(
      "structural patterns",
      pattern,
      Extensions.StructuralPatterns,
      accept
    );
  }

  checkPatternAsc(pattern: PatternAsc, accept: ValidationAcceptor): void {
    this.requireExtension(
      "pattern ascriptions",
      pattern,
      Extensions.PatternAscriptions,
      accept
    );
  }

  checkPatternCastAs(pattern: PatternCastAs, accept: ValidationAcceptor): void {
    this.requireExtension(
      "pattern casting",
      pattern,
      Extensions.TypeCastPatterns,
      accept
    );
  }

  checkPatternSumTypes(
    pattern: PatternInl | PatternInr,
    accept: ValidationAcceptor
  ): void {
    this.checkSumTypes(pattern, accept);
    if (!isPatternVar(pattern.pattern)) {
      this.checkStructuralPatterns(pattern.pattern, accept);
    }
  }

  checkPatternVariant(
    pattern: PatternVariant,
    accept: ValidationAcceptor
  ): void {
    this.requireExtension(
      "variant patterns",
      pattern,
      Extensions.Variants,
      accept
    );

    if (pattern.pattern === undefined) {
      this.requireExtension(
        "nullary variant label patterns",
        pattern,
        Extensions.NullaryVariantLabels,
        accept
      );
    } else {
      this.checkStructuralPatterns(pattern.pattern, accept);
    }
  }

  checkPatternTuple(tuple: PatternTuple, accept: ValidationAcceptor): void {
    this.checkStructuralPatterns(tuple, accept);

    if (tuple.patterns.length === 2) {
      this.requireExtension(
        "pairs patterns",
        tuple,
        [Extensions.Pairs, Extensions.Tuples],
        accept
      );
    } else {
      this.requireExtension(
        "tuples patterns",
        tuple,
        Extensions.Tuples,
        accept
      );
    }
  }

  checkPatternRecord(node: PatternRecord, accept: ValidationAcceptor): void {
    this.requireExtension("record patterns", node, Extensions.Records, accept);
    this.checkStructuralPatterns(node, accept);
  }

  checkPatternList(
    pattern: PatternList | PatternCons,
    accept: ValidationAcceptor
  ): void {
    this.checkStructuralPatterns(pattern, accept);
    this.requireExtension("lists patterns", pattern, Extensions.Lists, accept);
  }

  checkPatternInt(pattern: PatternInt, accept: ValidationAcceptor): void {
    this.checkStructuralPatterns(pattern, accept);
    if (pattern.n < 0) {
      this.requireExtension(
        "integer patterns",
        pattern,
        Extensions.Integers,
        accept
      );
    }
  }

  // Expressions

  checkConstUnit(unit: ConstUnit, accept: ValidationAcceptor): void {
    this.requireExtension("unit", unit, Extensions.UnitType, accept);
  }

  checkConstInt(node: ConstInt, accept: ValidationAcceptor): void {
    if (node.n === 0) return;
    if (node.n > 0) {
      this.requireExtension(
        "natural numbers",
        node,
        [Extensions.NaturalLiterals, Extensions.Integers],
        accept
      );
    } else {
      this.requireExtension("integers", node, Extensions.Integers, accept);
    }
  }

  checkApplication(app: Application, accept: ValidationAcceptor): void {
    if (app.args.length < 1) {
      this.requireExtension(
        "nullary functions",
        app,
        Extensions.NullaryFunctions,
        accept
      );
    } else if (app.args.length > 1) {
      this.requireExtension(
        "multi-parameter functions",
        app.args[0],
        Extensions.MultiparameterFunctions,
        accept
      );
    }
  }

  checkSequence(node: Sequence, accept: ValidationAcceptor): void {
    this.requireExtension("sequencing", node, Extensions.Sequencing, accept);
  }

  checkLetBindings(node: Let, accept: ValidationAcceptor): void {
    this.requireExtension("let-bindings", node, Extensions.LetBindings, accept);
    if (node.patternBindings.length > 1) {
      this.requireExtension(
        "let-bindings with multiple bindings",
        node,
        Extensions.LetManyBindings,
        accept
      );
    }
    if (!node.patternBindings.every(isPatternVar)) {
      this.requireExtension(
        "let-bindings with patterns",
        node,
        Extensions.LetPatterns,
        accept
      );
    }
  }

  checkLetRecBindings(node: LetRec, accept: ValidationAcceptor): void {
    this.requireExtension(
      "letrec-bindings",
      node,
      Extensions.LetrecBindings,
      accept
    );
    if (node.patternBindings.length > 1) {
      this.requireExtension(
        "letrec-bindings with multiple bindings",
        node,
        Extensions.LetrecManyBindings,
        accept
      );
    }
    if (!node.patternBindings.every(isPatternVar)) {
      this.requireExtension(
        "letrec-bindings with patterns",
        node,
        Extensions.LetPatterns,
        accept
      );
    }
  }

  checkTypeAsc(node: TypeAsc, accept: ValidationAcceptor): void {
    this.requireExtension(
      "type ascriptions",
      node,
      Extensions.TypeAscriptions,
      accept
    );
  }

  checkTuple(tuple: Tuple, accept: ValidationAcceptor): void {
    if (tuple.exprs.length === 2) {
      this.requireExtension(
        "pairs",
        tuple,
        [Extensions.Pairs, Extensions.Tuples],
        accept
      );
    } else {
      this.requireExtension("tuples", tuple, Extensions.Tuples, accept);
    }
  }

  checkRecord(record: Record | DotRecord, accept: ValidationAcceptor): void {
    this.requireExtension("records", record, Extensions.Records, accept);
  }

  checkSumTypes(
    node: Inl | Inr | PatternInl | PatternInr,
    accept: ValidationAcceptor
  ): void {
    this.requireExtension("sum types", node, Extensions.SumTypes, accept);
  }

  checkVariant(variant: Variant, accept: ValidationAcceptor): void {
    this.requireExtension("variants", variant, Extensions.Variants, accept);

    if (variant.rhs === undefined) {
      this.requireExtension(
        "nullary variant label",
        variant,
        Extensions.NullaryVariantLabels,
        accept
      );
    }
  }

  checkArithmetic(
    node: Add | Subtraction | Multiply | Divide,
    accept: ValidationAcceptor
  ): void {
    this.requireExtension(
      "arithmetic operations",
      node,
      Extensions.ArithmeticOperators,
      accept
    );
  }

  checkList(
    list: List | ConsList | Head | IsEmpty | Tail,
    accept: ValidationAcceptor
  ): void {
    this.requireExtension("lists", list, Extensions.Lists, accept);
  }

  checkPred(node: Pred, accept: ValidationAcceptor): void {
    this.requireExtension("predecessor", node, Extensions.Predecessor, accept);
  }

  checkFix(node: Fix, accept: ValidationAcceptor): void {
    this.requireExtension(
      "fix",
      node,
      [Extensions.FixpointCombinator, Extensions.GeneralRecursion],
      accept
    );
  }

  checkIsorecursiveTypes(
    node: Fold | Unfold,
    accept: ValidationAcceptor
  ): void {
    this.requireExtension(
      "fold / unfold",
      node,
      Extensions.IsorecursiveTypes,
      accept
    );
  }

  checkDotTuple(tuple: DotTuple, accept: ValidationAcceptor): void {
    if (tuple.index > 2) {
      this.requireExtension("tuples", tuple, Extensions.Tuples, accept);
    } else {
      this.requireExtension(
        "pairs",
        tuple,
        [Extensions.Pairs, Extensions.Tuples],
        accept
      );
    }
  }

  checkLogicalOperators(
    node: LogicOr | LogicAnd | LogicNot,
    accept: ValidationAcceptor
  ): void {
    this.requireExtension(
      "logical operators",
      node,
      Extensions.LogicalOperators,
      accept
    );
  }

  checkComparisonOperators(
    node:
      | LessThan
      | LessThanOrEqual
      | GreaterThan
      | GreaterThanOrEqual
      | Equal
      | NotEqual,
    accept: ValidationAcceptor
  ): void {
    this.requireExtension(
      "comparison operators",
      node,
      Extensions.ComparisonOperators,
      accept
    );
  }

  checkReferences(
    node: Assign | Ref | Deref | ConstMemory,
    accept: ValidationAcceptor
  ): void {
    this.requireExtension("references", node, Extensions.References, accept);
  }

  checkTypeCast(node: TypeCast, accept: ValidationAcceptor): void {
    this.requireExtension("type cast", node, Extensions.TypeCast, accept);
  }

  checkPanic(node: Panic, accept: ValidationAcceptor): void {
    this.requireExtension("panic", node, Extensions.Panic, accept);
  }

  checkExceptions(
    node: Throw | TryCatch | TryWith,
    accept: ValidationAcceptor
  ): void {
    this.requireExtension("exceptions", node, Extensions.Exceptions, accept);
  }

  checkTryCastAs(node: TryCastAs, accept: ValidationAcceptor): void {
    this.requireExtension("try-cast-as", node, Extensions.TryCastAs, accept);
  }

  checkUniversalTypes(
    node: TypeAbstraction | TypeApplication,
    accept: ValidationAcceptor
  ): void {
    this.requireExtension(
      "universal types",
      node,
      Extensions.UniversalTypes,
      accept
    );
  }

  // Types

  checkTypeAuto(node: TypeAuto, accept: ValidationAcceptor): void {
    this.requireExtension(
      "type reconstruction",
      node,
      Extensions.TypeReconstruction,
      accept
    );
  }

  checkTypeFun(node: TypeFun, accept: ValidationAcceptor): void {
    if (node.paramTypes.length < 1) {
      this.requireExtension(
        "nullary functions",
        node,
        Extensions.NullaryFunctions,
        accept
      );
    } else if (node.paramTypes.length > 1) {
      this.requireExtension(
        "multi-parameter functions",
        node,
        Extensions.MultiparameterFunctions,
        accept
      );
    }
  }

  checkTypeRec(node: TypeRec, accept: ValidationAcceptor): void {
    this.requireExtension(
      "recursive types",
      node,
      [
        Extensions.RecursiveTypes,
        Extensions.IsorecursiveTypes,
        Extensions.EquirecursiveTypes,
      ],
      accept
    );
  }

  checkTypeSum(node: TypeSum, accept: ValidationAcceptor): void {
    if (node.$type !== "TypeSum") return;
    this.requireExtension("sum types", node, Extensions.SumTypes, accept);
  }

  checkTypeTuple(node: TypeTuple, accept: ValidationAcceptor): void {
    if (node.types.length === 2) {
      this.requireExtension(
        "pairs",
        node,
        [Extensions.Pairs, Extensions.Tuples],
        accept
      );
    } else {
      this.requireExtension("tuples", node, Extensions.Tuples, accept);
    }
  }

  checkTypeRecord(node: TypeRecord, accept: ValidationAcceptor): void {
    this.requireExtension("record types", node, Extensions.Records, accept);
  }

  checkTypeVariant(node: TypeVariant, accept: ValidationAcceptor): void {
    this.requireExtension("variant types", node, Extensions.Variants, accept);
  }

  checkTypeList(node: TypeList, accept: ValidationAcceptor): void {
    this.requireExtension("list types", node, Extensions.Lists, accept);
  }

  checkTypeUnit(node: TypeUnit, accept: ValidationAcceptor): void {
    this.requireExtension("unit types", node, Extensions.UnitType, accept);
  }

  checkTypeVar(node: TypeVar, accept: ValidationAcceptor): void {
    this.requireExtension(
      "type variables",
      node,
      [
        Extensions.TypeAliases,
        Extensions.RecursiveTypes,
        Extensions.UniversalTypes,
      ],
      accept
    );
  }

  checkTypeTop(node: TypeTop, accept: ValidationAcceptor): void {
    this.requireExtension("top type", node, Extensions.TopType, accept);
  }

  checkTypeBottom(node: TypeBottom, accept: ValidationAcceptor): void {
    this.requireExtension("bottom type", node, Extensions.BottomType, accept);
  }

  checkTypeRef(node: TypeRef, accept: ValidationAcceptor): void {
    this.requireExtension(
      "reference types",
      node,
      Extensions.References,
      accept
    );
  }

  checkTypeForAll(node: TypeForAll, accept: ValidationAcceptor): void {
    this.requireExtension(
      "for-all types",
      node,
      Extensions.UniversalTypes,
      accept
    );
  }
}
