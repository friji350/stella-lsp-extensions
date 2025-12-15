import { AstNode, AstUtils } from "langium";
import {
  NO_PARAMETER_NAME,
  InferenceRuleNotApplicable,
  isFunctionType,
} from "typir";
import type { Type as TypirType, TypirServices } from "typir";
import type {
  LangiumTypeSystemDefinition,
  TypirLangiumServices,
  TypirLangiumSpecifics,
} from "typir-langium";
import {
  type StellaAstType,
  isDeclFun,
  isVar,
  Var,
  ConstInt,
  ConstTrue,
  ConstFalse,
  TypeUnit,
  TypeAuto,
  TypeBottom,
  Succ,
  IsZero,
  Deref,
  Application,
  DeclFun,
  TypeNat,
  TypeBool,
  ConstUnit,
  Inl,
  Inr,
  Match,
  MatchCase,
  // Let,
  PatternInl,
  PatternInr, 
  PatternVar,
  TypeList,
  List,
  ConsList,
  Head,
  Tail,
  IsEmpty,

  isPatternBinding,
} from "../generated/ast.js";

export interface StellaSpecifics extends TypirLangiumSpecifics {
  AstTypes: StellaAstType; // all AST types from the generated `ast.ts`
}

export type TypirStellaServices = TypirLangiumServices<StellaSpecifics>;

export class StellaTypeSystem
  implements LangiumTypeSystemDefinition<StellaSpecifics>
{
  onInitialize(typir: TypirStellaServices): void {
    // Register primitive types
    const typeNat = typir.factory.Primitives.create({
      // The name here doesn't have to correspond to the name in the grammar, what matters is the inference rule
      primitiveName: "Nat",
    })
      .inferenceRule({ languageKey: ConstInt.$type })
      .inferenceRule({ languageKey: TypeNat.$type }) // I don't like that "Nat" has type "Nat", but not sure what's it supposed to be
      .finish();

    const typeBool = typir.factory.Primitives.create({
      primitiveName: "Bool",
    })
      .inferenceRule({ languageKey: [ConstTrue.$type, ConstFalse.$type] })
      .inferenceRule({ languageKey: TypeBool.$type })
      .finish();

    typir.factory.Primitives.create({ primitiveName: "Unit" })
      .inferenceRule({ languageKey: ConstUnit.$type })
      .inferenceRule({ languageKey: TypeUnit.$type })
      .finish();

    // TODO: is auto really a "primitive" type? Is there a distinction between primitive and built-in types in Typir?
    const typeAuto = typir.factory.Primitives.create({
      primitiveName: "auto",
    })
      .inferenceRule({ languageKey: TypeAuto.$type })
      .finish();

    const tupleTypeCache = new Map<string, TypirType>();
    const tupleTypeLookup = new Map<TypirType, TypirType[]>();
    const sumTypeCache = new Map<string, TypirType>();
    const sumTypeLookup = new Map<TypirType, [TypirType, TypirType]>();

    const areTypesEqual = (left: TypirType, right: TypirType): boolean =>
      !typir.Equality.getTypeEqualityProblem(left, right);

    const tupleTypeKey = (componentTypes: TypirType[]) =>
      componentTypes.map((type) => type.getIdentifier()).join("|");

    const tuplePrimitiveName = (componentTypes: TypirType[]) =>
      `Tuple<${componentTypes
        .map((type) => typir.Printer.printTypeName(type))
        .join(", ")}>`;

    const getOrCreateTupleType = (
      componentTypes: TypirType[],
      associatedLanguageNode?: AstNode
    ): TypirType => {
      const key = tupleTypeKey(componentTypes);
      const cached = tupleTypeCache.get(key);
      if (cached) {
        return cached;
      }

      const tupleType = typir.factory.Primitives.create({
        primitiveName: `${tuplePrimitiveName(componentTypes)}#${key}`,
        associatedLanguageNode,
      }).finish();
      tupleTypeCache.set(key, tupleType);
      tupleTypeLookup.set(tupleType, componentTypes.slice());
      return tupleType;
    };
    const sumTypeKey = (left: TypirType, right: TypirType) =>
      `${left.getIdentifier()}+${right.getIdentifier()}`;

    const sumPrimitiveName = (left: TypirType, right: TypirType) =>
      `Sum<${typir.Printer.printTypeName(left)}, ${typir.Printer.printTypeName(
        right
      )}>`;

    const getOrCreateSumType = (
      left: TypirType,
      right: TypirType,
      associatedLanguageNode?: AstNode
    ): TypirType => {
      const key = sumTypeKey(left, right);
      const cached = sumTypeCache.get(key);
      if (cached) {
        return cached;
      }

      const sumType = typir.factory.Primitives.create({
        primitiveName: `${sumPrimitiveName(left, right)}#${key}`,
        associatedLanguageNode,
      }).finish();
      sumTypeCache.set(key, sumType);
      sumTypeLookup.set(sumType, [left, right]);
      return sumType;
    };
    const listTypeCache = new Map<string, TypirType>();
    const listTypeLookup = new Map<TypirType, TypirType>();

    const listTypeKey = (elementType: TypirType) =>
      `${elementType.getIdentifier()}`;

    const listPrimitiveName = (elementType: TypirType) =>
      `List<${typir.Printer.printTypeName(elementType)}>`;

    const getOrCreateListType = (
      elementType: TypirType,
      associatedLanguageNode?: AstNode
    ): TypirType => {
      const key = listTypeKey(elementType);
      const cached = listTypeCache.get(key);
      if (cached) {
        return cached;
      }

      const listType = typir.factory.Primitives.create({
        primitiveName: `${listPrimitiveName(elementType)}#${key}`,
        associatedLanguageNode,
      }).finish();
      listTypeCache.set(key, listType);
      listTypeLookup.set(listType, elementType);
      return listType;
    };
    
    const functionTypeCache = new Map<string, TypirType>();

    const functionTypeKey = (
      paramTypes: TypirType[],
      returnType: TypirType
    ): string =>
      `${paramTypes.map((type) => type.getIdentifier()).join("|")}->${returnType.getIdentifier()}`;

    const functionPrimitiveName = (
      paramTypes: TypirType[],
      returnType: TypirType
    ) =>
      `Fn<(${paramTypes
        .map((type) => typir.Printer.printTypeName(type))
        .join(", ")}) -> ${typir.Printer.printTypeName(returnType)}>`;

    const getOrCreateFunctionType = (
      paramTypes: TypirType[],
      returnType: TypirType,
      associatedLanguageNode?: AstNode
    ): TypirType => {
      const key = functionTypeKey(paramTypes, returnType);
      const cached = functionTypeCache.get(key);
      if (cached) {
        return cached;
      }

      const functionInitializer = typir.factory.Functions.create({
        functionName: `${functionPrimitiveName(paramTypes, returnType)}#${key}`,
        inputParameters: paramTypes.map((type, index) => ({
          name: `arg${index}`,
          type,
        })),
        outputParameter: {
          name: NO_PARAMETER_NAME,
          type: returnType,
        },
        associatedLanguageNode,
      }).finish();
      const functionType = functionInitializer.getTypeInitial();
      functionTypeCache.set(key, functionType);
      return functionType;
    };
    

    // const pairClass = typir.factory.Classes.create({
    // className: 'Pair',
    // fields: [
    //   { name: 'fst', type: typeAuto }, // плюс другие обязательные поля, если есть
    //   { name: 'snd', type: typeAuto },
    // ],
    // methods: [],
    // })
    // .finish();

    // Top and bottom
    // TODO: I'm probably using inference rules incorrectly ??
    // const typeTop = typir.factory.Top.create({})
    //   .inferenceRule({ languageKey: TypeTop.$type })
    //   .finish();

    const typeBottom = typir.factory.Bottom.create({})
      .inferenceRule({ languageKey: TypeBottom.$type })
      .finish();

    // Unary operators
    // TODO: also needs generics
    typir.factory.Operators.createUnary({
      name: "Dereference",
      signature: {
        operand: typeAuto, // TODO: generics are not yet supported in Typir :(
        return: typeBottom,
      },
    })
      .inferenceRule<Deref>({
        languageKey: Deref.$type,
        matching: () => true,
        // The type of a dereference is the type of the variable it points to
        operand: (deref) => deref.expr,
      })
      .finish();

    // Binary operators
    typir.factory.Operators.createBinary;

    // Ternary operators
    

    // Built-in functions
    typir.factory.Functions.create({
      functionName: "succ",
      inputParameters: [{ name: "n", type: typeNat }],
      outputParameter: {
        name: NO_PARAMETER_NAME,
        type: typeNat,
      },
    })
      .inferenceRuleForCalls<Succ>({
        languageKey: Succ.$type,
        inputArguments: (node) => [node.n],
      })
      .finish();

    typir.factory.Functions.create({
      functionName: "Nat::iszero",
      inputParameters: [{ name: "n", type: typeNat }],
      outputParameter: {
        name: NO_PARAMETER_NAME,
        type: typeBool,
      },
    }).inferenceRuleForCalls<IsZero>({
      languageKey: IsZero.$type,
      inputArguments: (node) => [node.n],
    })
    .finish();
    // List primitives and operations are handled through cached element-specific types

    // Inference rules
    typir.Inference.addInferenceRulesForAstNodes({
      Var: (node) => node.ref.ref ?? InferenceRuleNotApplicable, // The type of a variable is the type of the declaration it points to
      Application: (node) => {
        if (isVar(node.fun)) {
          const decl = node.fun.ref.ref as DeclFun | undefined;
          return decl?.returnType ?? InferenceRuleNotApplicable;
        }
        return InferenceRuleNotApplicable;
      },
      ParamDecl: (node) => node.paramType,
      TypeTuple: (node, typir) => {
        if (node.types.length !== 2) return InferenceRuleNotApplicable;

        const componentTypes: TypirType[] = [];
        for (const component of node.types) {
          const componentType = typir.Inference.inferType(component);
          if (Array.isArray(componentType)) return InferenceRuleNotApplicable;
          componentTypes.push(componentType);
        }

        return getOrCreateTupleType(componentTypes, node);
      },
      TypeFun: (node, typir) => {
        const paramTypes: TypirType[] = [];
        for (const param of node.paramTypes) {
          const paramType = typir.Inference.inferType(param);
          if (Array.isArray(paramType)) return InferenceRuleNotApplicable;
          paramTypes.push(paramType);
        }

        const returnType = typir.Inference.inferType(node.returnType);
        if (Array.isArray(returnType)) return InferenceRuleNotApplicable;

        return getOrCreateFunctionType(paramTypes, returnType, node);
      },
      Tuple: (node, typir) => {
        if (node.exprs.length !== 2) return InferenceRuleNotApplicable;

        const componentTypes: TypirType[] = [];
        for (const expr of node.exprs) {
          const exprType = typir.Inference.inferType(expr);
          if (Array.isArray(exprType)) return InferenceRuleNotApplicable;
          componentTypes.push(exprType);
        }

        return getOrCreateTupleType(componentTypes, node);
      },
      DotTuple: (node, typir) => {
        const tupleType = typir.Inference.inferType(node.expr);
        if (Array.isArray(tupleType)) return InferenceRuleNotApplicable;

        const components = tupleTypeLookup.get(tupleType);
        if (!components) return InferenceRuleNotApplicable;

        const componentIndex = node.index - 1;
        if (componentIndex < 0 || componentIndex >= components.length) {
          return InferenceRuleNotApplicable;
        }

        return components[componentIndex];
      },
      Abstraction: (node, typir) => {
        const paramTypes: TypirType[] = [];
        for (const param of node.paramDecls) {
          if (!param.paramType) return InferenceRuleNotApplicable;
          const paramType = typir.Inference.inferType(param.paramType);
          if (Array.isArray(paramType)) return InferenceRuleNotApplicable;
          paramTypes.push(paramType);
        }

        const returnType = typir.Inference.inferType(node.returnExpr);
        if (Array.isArray(returnType)) return InferenceRuleNotApplicable;

        return getOrCreateFunctionType(paramTypes, returnType, node);
      },
      NatRec: (node, typir) => {
        const nType = typir.Inference.inferType(node.n);
        if (Array.isArray(nType) || nType !== typeNat) {
          return InferenceRuleNotApplicable;
        }

        const initialType = typir.Inference.inferType(node.initial);
        if (Array.isArray(initialType)) return InferenceRuleNotApplicable;

        const stepType = typir.Inference.inferType(node.step);
        if (Array.isArray(stepType)) return InferenceRuleNotApplicable;

        return initialType;
      },
      Succ: () => {
        return typeNat ?? InferenceRuleNotApplicable;
      },
      IsZero: () => {
        return typeBool ?? InferenceRuleNotApplicable;
      },
      TypeSum: (node, typir) => {
        const leftType = typir.Inference.inferType(node.left);
        if (Array.isArray(leftType)) return InferenceRuleNotApplicable;
        const rightType = typir.Inference.inferType(node.right);
        if (Array.isArray(rightType)) return InferenceRuleNotApplicable;

        return getOrCreateSumType(leftType, rightType, node);
      },
      TypeList: (node, typir) => {
        const elementType = typir.Inference.inferType(node.type);
        if (Array.isArray(elementType)) return InferenceRuleNotApplicable;
        return getOrCreateListType(elementType, node);
      },
      List: (node, typir) => {
        if (node.exprs.length === 0) {
          const expected = getExpectedListType(node, typir, listTypeLookup);
          if (!expected || Array.isArray(expected)) {
            return InferenceRuleNotApplicable;
          }
          return expected;
        }

        const elementTypes: TypirType[] = [];
        for (const expr of node.exprs) {
          const exprType = typir.Inference.inferType(expr);
          if (Array.isArray(exprType) || !exprType) {
            return InferenceRuleNotApplicable;
          }
          elementTypes.push(exprType);
        }

        const reference = elementTypes[0];
        for (const elementType of elementTypes.slice(1)) {
          if (!areTypesEqual(reference, elementType)) {
            return InferenceRuleNotApplicable;
          }
        }

        return getOrCreateListType(reference, node);
      },
      ConsList: (node, typir) => {
        const tailType = typir.Inference.inferType(node.tail);
        if (Array.isArray(tailType) || !tailType) {
          return InferenceRuleNotApplicable;
        }

        const elementType = listTypeLookup.get(tailType);
        if (!elementType) return InferenceRuleNotApplicable;

        const headType = typir.Inference.inferType(node.head);
        if (Array.isArray(headType) || !headType) {
          return InferenceRuleNotApplicable;
        }

        if (!areTypesEqual(headType, elementType)) {
          return InferenceRuleNotApplicable;
        }

        return tailType;
      },
      Head: (node, typir) => {
        const listType = typir.Inference.inferType(node.list);
        if (Array.isArray(listType) || !listType) {
          return InferenceRuleNotApplicable;
        }

        const elementType = listTypeLookup.get(listType);
        if (!elementType) return InferenceRuleNotApplicable;

        return elementType;
      },
      Tail: (node, typir) => {
        const listType = typir.Inference.inferType(node.list);
        if (Array.isArray(listType) || !listType) {
          return InferenceRuleNotApplicable;
        }

        if (!listTypeLookup.has(listType)) return InferenceRuleNotApplicable;

        return listType;
      },
      IsEmpty: (node, typir) => {
        const listType = typir.Inference.inferType(node.list);
        if (Array.isArray(listType) || !listType) {
          return InferenceRuleNotApplicable;
        }

        if (!listTypeLookup.has(listType)) return InferenceRuleNotApplicable;

        return typeBool ?? InferenceRuleNotApplicable;
      },
      Inl: (node, typir) => {
        const expectedSum = getExpectedSumType(node, typir, sumTypeLookup);
        if (!expectedSum || Array.isArray(expectedSum)) {
          return InferenceRuleNotApplicable;
        }

        return expectedSum;
      },
      Inr: (node, typir) => {
        const expectedSum = getExpectedSumType(node, typir, sumTypeLookup);
        if (!expectedSum || Array.isArray(expectedSum)) {
          return InferenceRuleNotApplicable;
        }

        return expectedSum;
      },
      Match: (node, typir) => {
        const branchTypes: TypirType[] = [];
        for (const matchCase of node.cases) {
          const exprType = typir.Inference.inferType(matchCase.expr);
          if (Array.isArray(exprType)) return InferenceRuleNotApplicable;
          if (!exprType) return InferenceRuleNotApplicable;
          branchTypes.push(exprType);
        }

        if (branchTypes.length === 0) {
          return InferenceRuleNotApplicable;
        }

        const first = branchTypes[0];
        for (const branchType of branchTypes.slice(1)) {
          if (!areTypesEqual(first, branchType)) {
            return InferenceRuleNotApplicable;
          }
        }

        return first;
      },
      If: (node, typir) => {
        const cond = typir.Inference.inferType(node.condition);
        if (Array.isArray(cond) || cond !== typeBool) return InferenceRuleNotApplicable;

        const t1 = typir.Inference.inferType(node.thenExpr);
        if (Array.isArray(t1)) return InferenceRuleNotApplicable;

        const t2 = typir.Inference.inferType(node.elseExpr);
        if (Array.isArray(t2)) return InferenceRuleNotApplicable;

        if (t1 !== t2) return InferenceRuleNotApplicable;

        return t1;
        },
      PatternVar: (node, typir) => {
        const binding = AstUtils.getContainerOfType(node, isPatternBinding);
        if (!binding) return InferenceRuleNotApplicable;

        const rhs = binding.rhs;
        if (!rhs) return InferenceRuleNotApplicable;

        const rhsType = typir.Inference.inferType(rhs);
        if (Array.isArray(rhsType)) return InferenceRuleNotApplicable;

        return rhsType;
      },

      Let: (node, typir) => {
        const bodyType = typir.Inference.inferType(node.body);
        if (Array.isArray(bodyType)) return InferenceRuleNotApplicable;
        return bodyType;
      },
      TypeAsc: (node, typir) => {
        const exprType = typir.Inference.inferType(node.expr);
        if (Array.isArray(exprType)) return InferenceRuleNotApplicable;

        const ascribedType = typir.Inference.inferType(node.type);
        if (Array.isArray(ascribedType)) return InferenceRuleNotApplicable;

        return ascribedType;
      },
      
    });

    // Additional validations
    // Return of a function must match the declared return type
    typir.validation.Collector.addValidationRulesForAstNodes({
      DeclFun: (node, accept, typir) => {
        typir.validation.Constraints.ensureNodeIsAssignable(
          node.returnExpr,
          node.returnType,
          accept,
          (actual, expected) => ({
            message: `The return type of function ${node.name} is ${actual.userRepresentation}, but the declared return type is ${expected.userRepresentation}`,
          })
        );

        if (!node.returnType) {
          return;
        }

        const declaredReturnType = typir.Inference.inferType(node.returnType);
        const actualReturnType = typir.Inference.inferType(node.returnExpr);

        if (
          !Array.isArray(declaredReturnType) &&
          !Array.isArray(actualReturnType) &&
          isFunctionType(declaredReturnType) &&
          isFunctionType(actualReturnType)
        ) {
          const expectedOutputRef =
            declaredReturnType.getOutput("RETURN_UNDEFINED")?.type;
          const actualOutputRef =
            actualReturnType.getOutput("RETURN_UNDEFINED")?.type;

          if (expectedOutputRef && actualOutputRef) {
            const resolver = typir.infrastructure.TypeResolver;
            const expectedOutput = resolver.resolve(expectedOutputRef);
            const actualOutput = resolver.resolve(actualOutputRef);

            if (!areTypesEqual(actualOutput, expectedOutput)) {
              accept({
                severity: "error",
                message: `The function body returns ${actualOutput.getName()}, but the declared return type is ${expectedOutput.getName()}`,
                languageNode: node.returnExpr,
              });
            }
          }
        }
      },

      If: (node, accept, typir) => {
        typir.validation.Constraints.ensureNodeIsAssignable(
          node.condition,
          typeBool,
          accept,
          (actual, expected) => ({
            message: `The condition of 'if' must have type ${expected.userRepresentation}, but it has type ${actual.userRepresentation}`,
          })
        );

        return typir.validation.Constraints.ensureNodeIsAssignable(
          node.elseExpr,
          node.thenExpr,
          accept,
          (actual, expected) => ({
            message: `The 'else' branch of 'if' must have type ${expected.userRepresentation}, but it has type ${actual.userRepresentation}`,
          })
        );
      },

      Succ: (node, accept, typir) => {
        return typir.validation.Constraints.ensureNodeIsAssignable(
          node.n,
          typeNat,
          accept,
          (actual, expected) => ({
            message: `'succ' expects its argument to have type ${expected.userRepresentation}, but it has type ${actual.userRepresentation}`,
          })
        );
      },

      IsZero: (node, accept, typir) => {
        return typir.validation.Constraints.ensureNodeIsAssignable(
          node.n,
          typeNat,
          accept,
          (actual, expected) => ({
            message: `'Nat::iszero' expects its argument to have type ${expected.userRepresentation}, but it has type ${actual.userRepresentation}`,
          })
        );
      },
      Abstraction: (node, accept, typir) => {
        const functionType = typir.Inference.inferType(node);
        if (Array.isArray(functionType) || !functionType) {
          return;
        }
        if (!isFunctionType(functionType)) {
          return;
        }

        const outputDescriptor =
          functionType.getOutput("RETURN_UNDEFINED")?.type;
        if (!outputDescriptor) {
          return;
        }

        const expectedReturnType =
          typir.infrastructure.TypeResolver.resolve(outputDescriptor);
        return typir.validation.Constraints.ensureNodeIsAssignable(
          node.returnExpr,
          expectedReturnType,
          accept,
          (actual, expected) => ({
            message: `The body of this lambda must have type ${expected.userRepresentation}, but it has type ${actual.userRepresentation}`,
          })
        );
      },
      TypeTuple: (node, accept) => {
        if (node.types.length !== 2) {
          accept({
            severity: "error",
            message: "Pairs must specify exactly two component types",
            languageNode: node,
          });
        }
      },
      TypeAsc: (node, accept, typir) => {
        return typir.validation.Constraints.ensureNodeIsAssignable(
          node.expr,
          node.type,
          accept,
          (actual, expected) => ({
            message: `An expression annotated with 'as' must have type ${expected.userRepresentation}, but it has type ${actual.userRepresentation}`,
          })
        );
      },
      Tuple: (node, accept) => {
        if (node.exprs.length !== 2) {
          accept({
            severity: "error",
            message: "Pairs must contain exactly two expressions",
            languageNode: node,
          });
        }
      },
      DotTuple: (node, accept, typir) => {
        if (node.index !== 1 && node.index !== 2) {
          accept({
            severity: "error",
            message: "Only '.1' and '.2' projections are defined for pairs",
            languageNode: node,
            languageProperty: "index",
          });
          return;
        }

        const tupleType = typir.Inference.inferType(node.expr);
        if (Array.isArray(tupleType)) {
          return;
        }

        const components = tupleType ? tupleTypeLookup.get(tupleType) : undefined;
        if (!components) {
          const actual = tupleType
            ? typir.Printer.printTypeUserRepresentation(tupleType)
            : "unknown";
          accept({
            severity: "error",
            message: `Pair projection expects a pair, but the expression has type ${actual}`,
            languageNode: node,
            languageProperty: "expr",
          });
          return;
        }

        const componentIndex = node.index - 1;
        if (componentIndex < 0 || componentIndex >= components.length) {
          accept({
            severity: "error",
            message: `Pair has only ${components.length} component(s), but '.${node.index}' was accessed`,
            languageNode: node,
            languageProperty: "index",
          });
        }
      },
      NatRec: (node, accept, typir) => {
        typir.validation.Constraints.ensureNodeIsAssignable(
          node.n,
          typeNat,
          accept,
          (actual, expected) => ({
            message: `The first argument of 'Nat::rec' must have type ${expected.userRepresentation}, but it has type ${actual.userRepresentation}`,
          })
        );

        const initialType = typir.Inference.inferType(node.initial);
        const stepType = typir.Inference.inferType(node.step);

        if (Array.isArray(initialType) || Array.isArray(stepType)) {
          return;
        }
        if (!initialType || !stepType) {
          return;
        }

        if (!isFunctionType(stepType)) {
          accept({
            severity: "error",
            message: `The step of 'Nat::rec' must be a function, but it has type ${typir.Printer.printTypeUserRepresentation(stepType)}`,
            languageNode: node.step,
          });
          return;
        }

        const stepInputs = stepType.getInputs();
        if (stepInputs.length < 1) {
          accept({
            severity: "error",
            message: "The step of 'Nat::rec' must accept the current iteration index of type Nat",
            languageNode: node.step,
          });
          return;
        }

        const resolver = typir.infrastructure.TypeResolver;
        const indexType = resolver.resolve(stepInputs[0].type);
        if (indexType !== typeNat) {
          accept({
            severity: "error",
            message: `The first parameter of the step in 'Nat::rec' must have type Nat, but it has type ${indexType.getName()}`,
            languageNode: node.step,
          });
          return;
        }

        const stepOutput = stepType.getOutput("RETURN_UNDEFINED")?.type;
        if (!stepOutput || !isFunctionType(stepOutput)) {
          accept({
            severity: "error",
            message:
              "The step of 'Nat::rec' must return a function that receives the accumulated result",
            languageNode: node.step,
          });
          return;
        }

        const accumulatorInputs = stepOutput.getInputs();
        if (accumulatorInputs.length < 1) {
          accept({
            severity: "error",
            message:
              "The inner function returned by the step of 'Nat::rec' must accept the current result",
            languageNode: node.step,
          });
          return;
        }

        const accumulatorType = resolver.resolve(accumulatorInputs[0].type);
        if (!areTypesEqual(accumulatorType, initialType)) {
          accept({
            severity: "error",
            message: `The accumulator parameter of the step in 'Nat::rec' must have type ${initialType.getName()}, but it has type ${accumulatorType.getName()}`,
            languageNode: node.step,
          });
          return;
        }

        const finalOutput = stepOutput.getOutput("RETURN_UNDEFINED")?.type;
        if (!finalOutput) {
          accept({
            severity: "error",
            message:
              "The inner function returned by the step of 'Nat::rec' must produce a result",
            languageNode: node.step,
          });
          return;
        }

        if (!areTypesEqual(finalOutput, initialType)) {
          accept({
            severity: "error",
            message: `The step of 'Nat::rec' must produce results of type ${initialType.getName()}, but it returns ${finalOutput.getName()}`,
            languageNode: node.step,
          });
        }
      },
      List: (node, accept, typir) => {
        if (node.exprs.length === 0) {
          const expected = getExpectedListType(node, typir, listTypeLookup);
          if (!expected) {
            accept({
              severity: "error",
              message:
                "Cannot infer the element type of an empty list. Add an annotation like '[] as [T]'.",
              languageNode: node,
            });
          }
          return;
        }

        const elementTypes: TypirType[] = [];
        for (const expr of node.exprs) {
          const exprType = typir.Inference.inferType(expr);
          if (Array.isArray(exprType) || !exprType) {
            return;
          }
          elementTypes.push(exprType);
        }

        const reference = elementTypes[0];
        for (let i = 1; i < elementTypes.length; i++) {
          const current = elementTypes[i];
          if (!areTypesEqual(reference, current)) {
            accept({
              severity: "error",
              message: `All list elements must have the same type. Expected ${reference.userRepresentation}, but element ${
                i + 1
              } has type ${current.userRepresentation}.`,
              languageNode: node.exprs[i],
            });
          }
        }
      },
      ConsList: (node, accept, typir) => {
        const tailType = typir.Inference.inferType(node.tail);
        if (Array.isArray(tailType) || !tailType) {
          return;
        }

        const elementType = listTypeLookup.get(tailType);
        if (!elementType) {
          accept({
            severity: "error",
            message: "'cons' expects the tail to be a list.",
            languageNode: node.tail,
          });
          return;
        }

        typir.validation.Constraints.ensureNodeIsAssignable(
          node.head,
          elementType,
          accept,
          (actual, expected) => ({
            message: `'cons' head must have type ${expected.userRepresentation}, but has ${actual.userRepresentation}.`,
          })
        );
      },
      Head: (node, accept, typir) => {
        const listType = typir.Inference.inferType(node.list);
        if (Array.isArray(listType)) {
          return;
        }
        const elementType = listType ? listTypeLookup.get(listType) : undefined;
        if (!elementType) {
          const actual = listType
            ? typir.Printer.printTypeUserRepresentation(listType)
            : "unknown";
          accept({
            severity: "error",
            message: `'List::head' expects a list, but got ${actual}.`,
            languageNode: node.list,
          });
        }
      },
      Tail: (node, accept, typir) => {
        const listType = typir.Inference.inferType(node.list);
        if (Array.isArray(listType)) {
          return;
        }
        if (!listType || !listTypeLookup.has(listType)) {
          const actual = listType
            ? typir.Printer.printTypeUserRepresentation(listType)
            : "unknown";
          accept({
            severity: "error",
            message: `'List::tail' expects a list, but got ${actual}.`,
            languageNode: node.list,
          });
        }
      },
      IsEmpty: (node, accept, typir) => {
        const listType = typir.Inference.inferType(node.list);
        if (Array.isArray(listType)) {
          return;
        }
        if (!listType || !listTypeLookup.has(listType)) {
          const actual = listType
            ? typir.Printer.printTypeUserRepresentation(listType)
            : "unknown";
          accept({
            severity: "error",
            message: `'List::isempty' expects a list, but got ${actual}.`,
            languageNode: node.list,
          });
        }
      },
      Inl: (node, accept, typir) => {
        const expectedSum = getExpectedSumType(node, typir, sumTypeLookup);
        if (!expectedSum || Array.isArray(expectedSum)) {
          accept({
            severity: "error",
            message:
              "It is not possible to output the amount type for 'inl'. Add an annotation of the form 'as <T + U>' or use it in the context of the expected type.",
            languageNode: node,
          });
          return;
        }

        const components = sumTypeLookup.get(expectedSum);
        if (!components) {
          return;
        }

        const [left] = components;
        typir.validation.Constraints.ensureNodeIsAssignable(
          node.expr,
          left,
          accept,
          (actual, expected) => ({
            message: `'inl' expected ${expected.userRepresentation}, but get ${actual.userRepresentation}`,
          })
        );
      },
      Inr: (node, accept, typir) => {
        const expectedSum = getExpectedSumType(node, typir, sumTypeLookup);
        if (!expectedSum || Array.isArray(expectedSum)) {
          accept({
            severity: "error",
            message:
              "It is not possible to output the amount type for 'inr'. Add an annotation of the form 'as <T + U>' or use it in the context of the expected type.",
            languageNode: node,
          });
          return;
        }

        const components = sumTypeLookup.get(expectedSum);
        if (!components) {
          return;
        }

        const [, right] = components;
        typir.validation.Constraints.ensureNodeIsAssignable(
          node.expr,
          right,
          accept,
          (actual, expected) => ({
            message: `'inr' expected ${expected.userRepresentation},but get ${actual.userRepresentation}`,
          })
        );
      },
      Match: (node, accept, typir) => {
        const scrutineeType = typir.Inference.inferType(node.expr);
        if (Array.isArray(scrutineeType) || !scrutineeType) {
          accept({
            severity: "error",
            message:
              "It is impossible to determine the type of the expression in 'match'. Add a type annotation or simplify the expression.",
            languageNode: node.expr,
          });
          return;
        }

        const sumComponents = sumTypeLookup.get(scrutineeType);
        if (!sumComponents) {
          accept({
            severity: "error",
            message:
              "The template matching with 'inl'/'inr' applies only to the summary type. Add '#sum-types' and specify the amount type.",
            languageNode: node.expr,
          });
          return;
        }

        let inlSeen = false;
        let inrSeen = false;

        const branchTypes: TypirType[] = [];
        for (const matchCase of node.cases) {
          const coverage = validatePatternAgainstSum(
            matchCase.pattern,
            sumComponents,
            accept,
            typir
          );
          inlSeen ||= coverage.inl;
          inrSeen ||= coverage.inr;

          const caseType = typir.Inference.inferType(matchCase.expr);
          if (Array.isArray(caseType) || !caseType) {
            continue;
          }
          branchTypes.push(caseType);
        }

        if (branchTypes.length < node.cases.length) {
          return;
        }

        const reference = branchTypes[0];
        for (const branchType of branchTypes.slice(1)) {
          if (!areTypesEqual(reference, branchType)) {
            accept({
              severity: "error",
              message:
                "All branches of the 'match' must return the same type.",
              languageNode: node,
            });
            return;
          }
        }

        if (!inlSeen || !inrSeen) {
          accept({
            severity: "error",
            message:
              "The total type should be split into both branches: 'inl' and 'inr' are expected.",
            languageNode: node,
          });
        }
      },
    });
  }

  onNewAstNode(node: AstNode, typir: TypirStellaServices): void {
    if (isDeclFun(node)) {
      typir.factory.Functions.create({
        functionName: node.name,
        inputParameters: node.paramDecls.map((decl) => ({
          name: decl.name,
          type: decl.paramType,
        })),
        outputParameter: {
          name: NO_PARAMETER_NAME,
          type: node.returnType!,
        },
        associatedLanguageNode: node,
      })
        .inferenceRuleForDeclaration({
          matching: (otherNode) => otherNode === node, // only the current function/method declaration matches
        })
        .inferenceRuleForCalls<Application>({
          languageKey: Application.$type,
          matching: (application) => {
            return (application.fun as Var)?.ref?.ref === node; 
          },
          inputArguments: (application) => application.args,
        });
    }
  }
}

function getExpectedSumType(
  node: Inl | Inr,
  typir: TypirServices<StellaSpecifics>,
  sumTypeLookup: Map<TypirType, [TypirType, TypirType]>
): TypirType | undefined {
  const container = node.$container as AstNode | undefined;
  if (!container) return undefined;

  // Ascription: (inl e) as T
  if ((container as { $type?: string; expr?: unknown }).$type === "TypeAsc") {
    const typeAsc = container as { type?: unknown; expr?: unknown };
    if (typeAsc.expr === node && typeAsc.type) {
      const expected = typir.Inference.inferType(typeAsc.type as AstNode);
      if (!Array.isArray(expected) && sumTypeLookup.has(expected)) {
        return expected;
      }
    }
  }

  // Function return position
  if (isDeclFun(container) && container.returnExpr === node && container.returnType) {
    const expected = typir.Inference.inferType(container.returnType);
    if (!Array.isArray(expected) && sumTypeLookup.has(expected)) {
      return expected;
    }
  }

  // Match branch expression
  if ((container as MatchCase).expr === node) {
    const matchNode = (container as MatchCase).$container as Match | undefined;
    if (matchNode) {
      const scrutinee = typir.Inference.inferType(matchNode.expr);
      if (!Array.isArray(scrutinee) && sumTypeLookup.has(scrutinee)) {
        return scrutinee;
      }
    }
  }

  return undefined;
}

function getExpectedListType(
  node: List,
  typir: TypirServices<StellaSpecifics>,
  listTypeLookup: Map<TypirType, TypirType>
): TypirType | undefined {
  const container = node.$container as AstNode | undefined;
  if (!container) return undefined;

  // Ascription: [] as [T]
  if ((container as { $type?: string; expr?: unknown }).$type === "TypeAsc") {
    const typeAsc = container as { type?: unknown; expr?: unknown };
    if (typeAsc.expr === node && typeAsc.type) {
      const expected = typir.Inference.inferType(typeAsc.type as AstNode);
      if (!Array.isArray(expected) && listTypeLookup.has(expected)) {
        return expected;
      }
    }
  }

  // Function return position
  if (isDeclFun(container) && container.returnExpr === node && container.returnType) {
    const expected = typir.Inference.inferType(container.returnType);
    if (!Array.isArray(expected) && listTypeLookup.has(expected)) {
      return expected;
    }
  }

  // Match branch expression
  if ((container as MatchCase).expr === node) {
    const matchNode = (container as MatchCase).$container as Match | undefined;
    if (matchNode) {
      const scrutinee = typir.Inference.inferType(matchNode.expr);
      if (!Array.isArray(scrutinee) && listTypeLookup.has(scrutinee)) {
        return scrutinee;
      }
    }
  }

  return undefined;
}

function validatePatternAgainstSum(
  pattern: PatternInl | PatternInr | PatternVar | AstNode,
  sumComponents: [TypirType, TypirType],
  accept: (diagnostic: {
    severity: "error" | "warning";
    message: string;
    languageNode: AstNode;
  }) => void,
  typir: TypirServices<StellaSpecifics>
): { inl: boolean; inr: boolean } {
  switch ((pattern as AstNode).$type) {
    case "PatternInl": {
      const inner = (pattern as PatternInl).pattern;
      if (inner.$type !== "PatternVar") {
        const expected = sumComponents[0];
        const innerType = typir.Inference.inferType(inner as AstNode);
        if (innerType && !Array.isArray(innerType) && !typir.Equality.getTypeEqualityProblem(innerType, expected)) {
      
        } else if (innerType && !Array.isArray(innerType)) {
          accept({
            severity: "error",
            message: `The 'inl' template expects a left-hand component of the type ${expected.getName()}.`,
            languageNode: inner as AstNode,
          });
        }
      }
      return { inl: true, inr: false };
    }
    case "PatternInr": {
      const inner = (pattern as PatternInr).pattern;
      if (inner.$type !== "PatternVar") {
        const expected = sumComponents[1];
        const innerType = typir.Inference.inferType(inner as AstNode);
        if (innerType && !Array.isArray(innerType) && !typir.Equality.getTypeEqualityProblem(innerType, expected)) {
          // ok
        } else if (innerType && !Array.isArray(innerType)) {
          accept({
            severity: "error",
            message: `The 'inr' template expects a right-hand component of the type ${expected.getName()}.`,
            languageNode: inner as AstNode,
          });
        }
      }
      return { inl: false, inr: true };
    }
    case "PatternVar":
      return { inl: true, inr: true };
    default:
      accept({
        severity: "error",
        message:
          "For the total type, the patterns 'inl', 'inr' or variable are acceptable.",
        languageNode: pattern as AstNode,
      });
      return { inl: false, inr: false };
  }
}
