import { AstNode, AstUtils } from "langium";
import {
  NO_PARAMETER_NAME,
  InferenceRuleNotApplicable,
  isFunctionType,
} from "typir";
import type {
  Type as TypirType,
  TypirServices,
  AnnotatedTypeAfterValidation,
} from "typir";
import type {
  LangiumTypeSystemDefinition,
  TypirLangiumServices,
  TypirLangiumSpecifics,
} from "typir-langium";
import {
  type StellaAstType,
  type Record as StellaRecord,
  Assign,
  ConstMemory,
  isDeclFun,
  isVar,
  Var,
  ConstInt,
  ConstTrue,
  ConstFalse,
  TypeUnit,
  TypeAuto,
  TypeTop,
  TypeBottom,
  Succ,
  IsZero,
  Application,
  DeclFun,
  TypeNat,
  TypeBool,
  ConstUnit,
  Inl,
  Inr,
  Match,
  MatchCase,
  Variant,
  PatternVariant,
  isMatchCase,
  // Let,
  PatternInl,
  PatternInr, 
  PatternVar,
  List,

  isPatternBinding,
} from "../generated/ast.js";
import { Extensions, getExtensions } from "../extensions.js";

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

    const typeUnit = typir.factory.Primitives.create({ primitiveName: "Unit" })
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
    const userRepr = (type: TypirType | AnnotatedTypeAfterValidation) =>
      "userRepresentation" in type
        ? type.userRepresentation
        : typir.Printer.printTypeUserRepresentation(type);
    const isAutoType = (type: TypirType | undefined | null): boolean =>
      type === typeAuto;
    const hasExtension = (node: AstNode, extension: Extensions): boolean => {
      const program = node.$document?.parseResult?.value;
      return program?.$type === "Program"
        ? getExtensions(program as never).has(extension)
        : false;
    };

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
        registerTupleSubtyping(cached);
        return cached;
      }

      const tupleType = typir.factory.Primitives.create({
        primitiveName: `${tuplePrimitiveName(componentTypes)}#${key}`,
        associatedLanguageNode,
      }).finish();
      tupleTypeCache.set(key, tupleType);
      tupleTypeLookup.set(tupleType, componentTypes.slice());
      registerAutoCompatibility(tupleType);
      registerTupleSubtyping(tupleType);
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
      registerAutoCompatibility(sumType);
      registerSumSubtyping(sumType);
      return sumType;
    };
    const recordTypeCache = new Map<string, TypirType>();
    const recordTypeLookup = new Map<TypirType, Map<string, TypirType>>();

    const recordFieldKey = (label: string, type: TypirType) =>
      `${label}:${type.getIdentifier()}`;

    const recordTypeKey = (fields: { label: string; type: TypirType }[]) =>
      fields
        .slice()
        .sort((a, b) => a.label.localeCompare(b.label))
        .map((field) => recordFieldKey(field.label, field.type))
        .join("|");

    const recordPrimitiveName = (fields: { label: string; type: TypirType }[]) =>
      `Record{${fields
        .slice()
        .sort((a, b) => a.label.localeCompare(b.label))
        .map(
          (field) =>
            `${field.label}: ${typir.Printer.printTypeName(field.type)}`
        )
        .join(", ")}}`;

    const getOrCreateRecordType = (
      fields: { label: string; type: TypirType }[],
      associatedLanguageNode?: AstNode
    ): TypirType => {
      const key = recordTypeKey(fields);
      const cached = recordTypeCache.get(key);
      if (cached) {
        registerRecordSubtyping(cached);
        return cached;
      }

      const recordType = typir.factory.Primitives.create({
        primitiveName: `${recordPrimitiveName(fields)}#${key}`,
        associatedLanguageNode,
      }).finish();
      recordTypeCache.set(key, recordType);

      const fieldMap = new Map<string, TypirType>();
      for (const field of fields) {
        fieldMap.set(field.label, field.type);
      }
      recordTypeLookup.set(recordType, fieldMap);
      registerAutoCompatibility(recordType);
      registerRecordSubtyping(recordType);
      return recordType;
    };
    const variantTypeCache = new Map<string, TypirType>();
    const variantTypeLookup = new Map<
      TypirType,
      Map<string, TypirType | undefined>
    >();

    const variantFieldKey = (label: string, type?: TypirType) =>
      `${label}:${type ? type.getIdentifier() : "nullary"}`;

    const variantTypeKey = (fields: { label: string; type?: TypirType }[]) =>
      fields
        .slice()
        .sort((a, b) => a.label.localeCompare(b.label))
        .map((field) => variantFieldKey(field.label, field.type))
        .join("|");

    const variantPrimitiveName = (
      fields: { label: string; type?: TypirType }[]
    ) =>
      `Variant<${fields
        .slice()
        .sort((a, b) => a.label.localeCompare(b.label))
        .map((field) =>
          field.type
            ? `${field.label}: ${typir.Printer.printTypeName(field.type)}`
            : `${field.label}`
        )
        .join(", ")}>`;

    const getOrCreateVariantType = (
      fields: { label: string; type?: TypirType }[],
      associatedLanguageNode?: AstNode
    ): TypirType => {
      const key = variantTypeKey(fields);
      const cached = variantTypeCache.get(key);
      if (cached) {
        return cached;
      }

      const variantType = typir.factory.Primitives.create({
        primitiveName: `${variantPrimitiveName(fields)}#${key}`,
        associatedLanguageNode,
      }).finish();
      variantTypeCache.set(key, variantType);

      const fieldMap = new Map<string, TypirType | undefined>();
      for (const field of fields) {
        fieldMap.set(field.label, field.type);
      }
      variantTypeLookup.set(variantType, fieldMap);
      registerAutoCompatibility(variantType);
      registerVariantSubtyping(variantType);
      return variantType;
    };
    const listTypeCache = new Map<string, TypirType>();
    const listTypeLookup = new Map<TypirType, TypirType>();
    const referenceTypeCache = new Map<string, TypirType>();
    const referenceTypeLookup = new Map<TypirType, TypirType>();

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
        registerListSubtyping(cached);
        return cached;
      }

      const listType = typir.factory.Primitives.create({
        primitiveName: `${listPrimitiveName(elementType)}#${key}`,
        associatedLanguageNode,
      }).finish();
      listTypeCache.set(key, listType);
      listTypeLookup.set(listType, elementType);
      registerAutoCompatibility(listType);
      registerListSubtyping(listType);
      return listType;
    };
    const referenceTypeKey = (referencedType: TypirType) =>
      `${referencedType.getIdentifier()}`;

    const referencePrimitiveName = (referencedType: TypirType) =>
      `Ref<${typir.Printer.printTypeName(referencedType)}>`;

    const getOrCreateReferenceType = (
      referencedType: TypirType,
      associatedLanguageNode?: AstNode
    ): TypirType => {
      const key = referenceTypeKey(referencedType);
      const cached = referenceTypeCache.get(key);
      if (cached) {
        registerReferenceSubtyping(cached);
        return cached;
      }

      const referenceType = typir.factory.Primitives.create({
        primitiveName: `${referencePrimitiveName(referencedType)}#${key}`,
        associatedLanguageNode,
      }).finish();
      referenceTypeCache.set(key, referenceType);
      referenceTypeLookup.set(referenceType, referencedType);
      registerAutoCompatibility(referenceType);
      registerReferenceSubtyping(referenceType);
      return referenceType;
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
        registerFunctionSubtyping(cached);
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
      registerAutoCompatibility(functionType);
      registerFunctionSubtyping(functionType);
      return functionType;
    };

    const markSubtypeIf = (subType: TypirType, superType: TypirType) => {
      if (subType === superType) {
        return;
      }
      if (!typir.Subtype.isSubType(subType, superType)) {
        typir.Subtype.markAsSubType(subType, superType, {
          checkForCycles: false,
        });
      }
    };
    const registerAutoCompatibility = (candidate: TypirType) => {
      markSubtypeIf(typeAuto, candidate);
    };
    const registerTupleSubtyping = (candidate: TypirType) => {
      const candidateComponents = tupleTypeLookup.get(candidate);
      if (!candidateComponents) {
        return;
      }

      for (const [otherType, otherComponents] of tupleTypeLookup.entries()) {
        if (candidateComponents.length !== otherComponents.length) {
          continue;
        }

        const candidateIsSubtype = candidateComponents.every((component, index) =>
          typir.Assignability.isAssignable(component, otherComponents[index])
        );
        if (candidateIsSubtype) {
          markSubtypeIf(candidate, otherType);
        }

        const otherIsSubtype = otherComponents.every((component, index) =>
          typir.Assignability.isAssignable(component, candidateComponents[index])
        );
        if (otherIsSubtype) {
          markSubtypeIf(otherType, candidate);
        }
      }
    };

    const registerSumSubtyping = (candidate: TypirType) => {
      const candidateComponents = sumTypeLookup.get(candidate);
      if (!candidateComponents) {
        return;
      }

      for (const [otherType, otherComponents] of sumTypeLookup.entries()) {
        const candidateIsSubtype =
          typir.Assignability.isAssignable(candidateComponents[0], otherComponents[0]) &&
          typir.Assignability.isAssignable(candidateComponents[1], otherComponents[1]);
        if (candidateIsSubtype) {
          markSubtypeIf(candidate, otherType);
        }

        const otherIsSubtype =
          typir.Assignability.isAssignable(otherComponents[0], candidateComponents[0]) &&
          typir.Assignability.isAssignable(otherComponents[1], candidateComponents[1]);
        if (otherIsSubtype) {
          markSubtypeIf(otherType, candidate);
        }
      }
    };

    const registerRecordSubtyping = (candidate: TypirType) => {
      const candidateFields = recordTypeLookup.get(candidate);
      if (!candidateFields) {
        return;
      }

      for (const [otherType, otherFields] of recordTypeLookup.entries()) {
        const candidateIsSubtype = [...otherFields.entries()].every(
          ([label, otherFieldType]) => {
            const candidateFieldType = candidateFields.get(label);
            return (
              candidateFieldType !== undefined &&
              typir.Assignability.isAssignable(candidateFieldType, otherFieldType)
            );
          }
        );
        if (candidateIsSubtype) {
          markSubtypeIf(candidate, otherType);
        }

        const otherIsSubtype = [...candidateFields.entries()].every(
          ([label, candidateFieldType]) => {
            const otherFieldType = otherFields.get(label);
            return (
              otherFieldType !== undefined &&
              typir.Assignability.isAssignable(otherFieldType, candidateFieldType)
            );
          }
        );
        if (otherIsSubtype) {
          markSubtypeIf(otherType, candidate);
        }
      }
    };

    const registerVariantSubtyping = (candidate: TypirType) => {
      const candidateFields = variantTypeLookup.get(candidate);
      if (!candidateFields) {
        return;
      }

      for (const [otherType, otherFields] of variantTypeLookup.entries()) {
        const candidateIsSubtype = [...candidateFields.entries()].every(
          ([label, candidatePayload]) => {
            if (!otherFields.has(label)) {
              return false;
            }

            const otherPayload = otherFields.get(label);
            if (candidatePayload === undefined || otherPayload === undefined) {
              return candidatePayload === otherPayload;
            }

            return typir.Assignability.isAssignable(candidatePayload, otherPayload);
          }
        );
        if (candidateIsSubtype) {
          markSubtypeIf(candidate, otherType);
        }

        const otherIsSubtype = [...otherFields.entries()].every(
          ([label, otherPayload]) => {
            if (!candidateFields.has(label)) {
              return false;
            }

            const candidatePayload = candidateFields.get(label);
            if (candidatePayload === undefined || otherPayload === undefined) {
              return candidatePayload === otherPayload;
            }

            return typir.Assignability.isAssignable(otherPayload, candidatePayload);
          }
        );
        if (otherIsSubtype) {
          markSubtypeIf(otherType, candidate);
        }
      }
    };

    const registerListSubtyping = (candidate: TypirType) => {
      const candidateElementType = listTypeLookup.get(candidate);
      if (!candidateElementType) {
        return;
      }

      for (const [otherType, otherElementType] of listTypeLookup.entries()) {
        if (typir.Assignability.isAssignable(candidateElementType, otherElementType)) {
          markSubtypeIf(candidate, otherType);
        }
        if (typir.Assignability.isAssignable(otherElementType, candidateElementType)) {
          markSubtypeIf(otherType, candidate);
        }
      }
    };

    const registerReferenceSubtyping = (candidate: TypirType) => {
      const candidateReferencedType = referenceTypeLookup.get(candidate);
      if (!candidateReferencedType) {
        return;
      }

      for (const [otherType, otherReferencedType] of referenceTypeLookup.entries()) {
        const candidateIsSubtype =
          typir.Assignability.isAssignable(candidateReferencedType, otherReferencedType) &&
          typir.Assignability.isAssignable(otherReferencedType, candidateReferencedType);
        if (candidateIsSubtype) {
          markSubtypeIf(candidate, otherType);
        }

        const otherIsSubtype =
          typir.Assignability.isAssignable(otherReferencedType, candidateReferencedType) &&
          typir.Assignability.isAssignable(candidateReferencedType, otherReferencedType);
        if (otherIsSubtype) {
          markSubtypeIf(otherType, candidate);
        }
      }
    };

    const registerFunctionSubtyping = (candidate: TypirType) => {
      if (!isFunctionType(candidate)) {
        return;
      }

      const candidateInputs = candidate.getInputs();
      const candidateOutput = candidate.getOutput("RETURN_UNDEFINED");
      if (!candidateOutput) {
        return;
      }

      for (const otherType of functionTypeCache.values()) {
        if (!isFunctionType(otherType)) {
          continue;
        }

        const otherInputs = otherType.getInputs();
        const otherOutput = otherType.getOutput("RETURN_UNDEFINED");
        if (!otherOutput || candidateInputs.length !== otherInputs.length) {
          continue;
        }

        const candidateIsSubtype =
          typir.Assignability.isAssignable(candidateOutput.type, otherOutput.type) &&
          candidateInputs.every((candidateInput, index) =>
            typir.Assignability.isAssignable(
              otherInputs[index].type,
              candidateInput.type
            )
          );
        if (candidateIsSubtype) {
          markSubtypeIf(candidate, otherType);
        }

        const otherIsSubtype =
          typir.Assignability.isAssignable(otherOutput.type, candidateOutput.type) &&
          otherInputs.every((otherInput, index) =>
            typir.Assignability.isAssignable(
              candidateInputs[index].type,
              otherInput.type
            )
          );
        if (otherIsSubtype) {
          markSubtypeIf(otherType, candidate);
        }
      }
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
    const typeTop = typir.factory.Top.create({})
      .inferenceRule({ languageKey: TypeTop.$type })
      .finish();

    const typeBottom = typir.factory.Bottom.create({})
      .inferenceRule({ languageKey: TypeBottom.$type })
      .finish();

    registerAutoCompatibility(typeNat);
    registerAutoCompatibility(typeBool);
    registerAutoCompatibility(typeUnit);
    registerAutoCompatibility(typeTop);
    registerAutoCompatibility(typeBottom);

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
      Application: (node, typir) => {
        if (isVar(node.fun)) {
          const referenced = node.fun.ref.ref as
            | (AstNode & {
                $type: "DeclFun" | "DeclFunGeneric";
                returnType?: AstNode;
              })
            | undefined;
          if (referenced?.returnType) {
            const declaredReturnType = typir.Inference.inferType(
              referenced.returnType
            );
            if (!Array.isArray(declaredReturnType) && declaredReturnType) {
              return declaredReturnType;
            }
          }
        }

        const functionType = getCallableType(node.fun, typir);
        if (!functionType) {
          return InferenceRuleNotApplicable;
        }
        if (!isFunctionType(functionType)) {
          return isAutoType(functionType) ? typeAuto : InferenceRuleNotApplicable;
        }

        if (functionType.getInputs().length !== node.args.length) {
          return InferenceRuleNotApplicable;
        }

        const outputDescriptor = functionType.getOutput("RETURN_UNDEFINED")?.type;
        if (!outputDescriptor) {
          return InferenceRuleNotApplicable;
        }

        return typir.infrastructure.TypeResolver.resolve(outputDescriptor);
      },
      ParamDecl: (node) => node.paramType,
      TypeTuple: (node, typir) => {
        if (node.types.length < 2) return InferenceRuleNotApplicable;

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
      TypeRef: (node, typir) => {
        const referencedType = typir.Inference.inferType(node.type);
        if (Array.isArray(referencedType) || !referencedType) {
          return InferenceRuleNotApplicable;
        }

        return getOrCreateReferenceType(referencedType, node);
      },
      Tuple: (node, typir) => {
        if (node.exprs.length < 2) return InferenceRuleNotApplicable;

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
      Record: (node, typir) => {
        const fields: { label: string; type: TypirType }[] = [];
        const seen = new Set<string>();

        for (const binding of node.bindings) {
          if (seen.has(binding.name)) return InferenceRuleNotApplicable;

          const fieldType = typir.Inference.inferType(binding.rhs);
          if (Array.isArray(fieldType) || !fieldType) {
            return InferenceRuleNotApplicable;
          }

          seen.add(binding.name);
          fields.push({ label: binding.name, type: fieldType });
        }

        return getOrCreateRecordType(fields, node);
      },
      DotRecord: (node, typir) => {
        const recordType = typir.Inference.inferType(node.expr);
        if (Array.isArray(recordType) || !recordType) {
          return InferenceRuleNotApplicable;
        }

        const fields = recordTypeLookup.get(recordType);
        if (!fields) return InferenceRuleNotApplicable;

        const fieldType = fields.get(node.label);
        if (!fieldType) return InferenceRuleNotApplicable;

        return fieldType;
      },
      Variant: (node, typir) => {
        const expected = getExpectedVariantType(
          node,
          typir,
          variantTypeLookup,
          referenceTypeLookup
        );
        if (!expected || Array.isArray(expected)) {
          return InferenceRuleNotApplicable;
        }

        return expected;
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
      TypeParens: (node, typir) => {
        const innerType = typir.Inference.inferType(node.type);
        if (Array.isArray(innerType)) return InferenceRuleNotApplicable;
        return innerType;
      },
      TypeRecord: (node, typir) => {
        const fields: { label: string; type: TypirType }[] = [];
        const seen = new Set<string>();

        for (const field of node.fieldTypes) {
          if (seen.has(field.label)) return InferenceRuleNotApplicable;

          const fieldType = typir.Inference.inferType(field.type);
          if (Array.isArray(fieldType)) return InferenceRuleNotApplicable;

          seen.add(field.label);
          fields.push({ label: field.label, type: fieldType });
        }

        return getOrCreateRecordType(fields, node);
      },
      TypeVariant: (node, typir) => {
        const fields: { label: string; type?: TypirType }[] = [];
        const seen = new Set<string>();

        for (const field of node.fieldTypes) {
          if (seen.has(field.label)) return InferenceRuleNotApplicable;

          let fieldType: TypirType | undefined;
          if (field.type) {
            const inferred = typir.Inference.inferType(field.type);
            if (Array.isArray(inferred)) return InferenceRuleNotApplicable;
            fieldType = inferred;
          }

          seen.add(field.label);
          fields.push({ label: field.label, type: fieldType });
        }

        return getOrCreateVariantType(fields, node);
      },
      TypeList: (node, typir) => {
        const elementType = typir.Inference.inferType(node.type);
        if (Array.isArray(elementType)) return InferenceRuleNotApplicable;
        return getOrCreateListType(elementType, node);
      },
      Ref: (node, typir) => {
        const referencedType = typir.Inference.inferType(node.expr);
        if (Array.isArray(referencedType) || !referencedType) {
          return InferenceRuleNotApplicable;
        }

        return getOrCreateReferenceType(referencedType, node);
      },
      Deref: (node, typir) => {
        const referenceType = typir.Inference.inferType(node.expr);
        if (Array.isArray(referenceType) || !referenceType) {
          return InferenceRuleNotApplicable;
        }

        return referenceTypeLookup.get(referenceType) ?? InferenceRuleNotApplicable;
      },
      Assign: (node, typir) => {
        const leftType = typir.Inference.inferType(node.left);
        if (Array.isArray(leftType) || !leftType) {
          return InferenceRuleNotApplicable;
        }

        return referenceTypeLookup.has(leftType)
          ? typeUnit
          : InferenceRuleNotApplicable;
      },
      Sequence: (node, typir) => {
        const secondType = typir.Inference.inferType(node.expr2);
        if (Array.isArray(secondType) || !secondType) {
          return InferenceRuleNotApplicable;
        }

        return secondType;
      },
      Panic: () => {
        return typeBottom;
      },
      Throw: () => {
        return typeBottom;
      },
      TryWith: (node, typir) => {
        const tryType = typir.Inference.inferType(node.tryExpr);
        if (Array.isArray(tryType) || !tryType) {
          return InferenceRuleNotApplicable;
        }

        const fallbackType = typir.Inference.inferType(node.fallbackExpr);
        if (Array.isArray(fallbackType) || !fallbackType) {
          return InferenceRuleNotApplicable;
        }

        return (
          getCompatibleExpressionType(
            tryType,
            fallbackType,
            typeBottom,
            areTypesEqual
          ) ?? InferenceRuleNotApplicable
        );
      },
      TryCatch: (node, typir) => {
        const tryType = typir.Inference.inferType(node.tryExpr);
        if (Array.isArray(tryType) || !tryType) {
          return InferenceRuleNotApplicable;
        }

        const fallbackType = typir.Inference.inferType(node.fallbackExpr);
        if (Array.isArray(fallbackType) || !fallbackType) {
          return InferenceRuleNotApplicable;
        }

        return (
          getCompatibleExpressionType(
            tryType,
            fallbackType,
            typeBottom,
            areTypesEqual
          ) ?? InferenceRuleNotApplicable
        );
      },
      ConstMemory: (node, typir) => {
        const expectedReferenceType = getExpectedReferenceType(
          node,
          typir,
          referenceTypeLookup
        );
        if (expectedReferenceType) {
          return expectedReferenceType;
        }

        const assign = node.$container;
        if (
          assign?.$type === Assign.$type &&
          assign.left === node
        ) {
          const assignedType = typir.Inference.inferType(assign.right);
          if (!Array.isArray(assignedType) && assignedType) {
            return getOrCreateReferenceType(assignedType, node);
          }
        }

        return InferenceRuleNotApplicable;
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

        const expectedListType = getExpectedListType(node, typir, listTypeLookup);
        const expectedElementType = expectedListType
          ? listTypeLookup.get(expectedListType)
          : undefined;

        const reference =
          expectedElementType ??
          elementTypes.find((type) => type !== typeAuto) ??
          elementTypes[0];
        for (const elementType of elementTypes.slice(1)) {
          if (
            reference !== typeAuto &&
            elementType !== typeAuto &&
            !areTypesEqual(reference, elementType)
          ) {
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

        const compatibleElementType =
          elementType === typeAuto
            ? headType
            : headType === typeAuto || areTypesEqual(headType, elementType)
              ? elementType
              : undefined;
        if (!compatibleElementType) {
          return InferenceRuleNotApplicable;
        }

        return getOrCreateListType(compatibleElementType, node);
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
        const expectedSum = getExpectedSumType(
          node,
          typir,
          sumTypeLookup,
          tupleTypeLookup
        );
        if (!expectedSum || Array.isArray(expectedSum)) {
          if (!hasExtension(node, Extensions.AmbiguousTypeAsBottom)) {
            return InferenceRuleNotApplicable;
          }

          const payloadType = typir.Inference.inferType(node.expr);
          if (Array.isArray(payloadType) || !payloadType) {
            return InferenceRuleNotApplicable;
          }

          return getOrCreateSumType(payloadType, typeBottom, node);
        }

        return expectedSum;
      },
      Inr: (node, typir) => {
        const expectedSum = getExpectedSumType(
          node,
          typir,
          sumTypeLookup,
          tupleTypeLookup
        );
        if (!expectedSum || Array.isArray(expectedSum)) {
          if (!hasExtension(node, Extensions.AmbiguousTypeAsBottom)) {
            return InferenceRuleNotApplicable;
          }

          const payloadType = typir.Inference.inferType(node.expr);
          if (Array.isArray(payloadType) || !payloadType) {
            return InferenceRuleNotApplicable;
          }

          return getOrCreateSumType(typeBottom, payloadType, node);
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
          if (
            !getCompatibleExpressionType(
              first,
              branchType,
              typeBottom,
              areTypesEqual
            )
          ) {
            return InferenceRuleNotApplicable;
          }
        }

        return branchTypes.reduce(
          (current, branchType) =>
            getCompatibleExpressionType(
              current,
              branchType,
              typeBottom,
              areTypesEqual
            ) ?? current,
          first
        );
      },
      Fix: (node, typir) => {
        const functionType = typir.Inference.inferType(node.expr);
        if (Array.isArray(functionType) || !functionType) {
          return InferenceRuleNotApplicable;
        }

        if (!isFunctionType(functionType)) {
          return InferenceRuleNotApplicable;
        }

        const inputs = functionType.getInputs();
        if (inputs.length !== 1) {
          return InferenceRuleNotApplicable;
        }

        const outputDescriptor = functionType.getOutput("RETURN_UNDEFINED")?.type;
        if (!outputDescriptor) {
          return InferenceRuleNotApplicable;
        }

        const resolver = typir.infrastructure.TypeResolver;
        const inputType = resolver.resolve(inputs[0].type);
        const outputType = resolver.resolve(outputDescriptor);

        return areTypesEqual(inputType, outputType)
          ? inputType
          : InferenceRuleNotApplicable;
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
        const expectedType = getExpectedPatternType(node, typir, {
          typeNat,
          typeBool,
          typeUnit,
          tupleTypeLookup,
          sumTypeLookup,
          recordTypeLookup,
          variantTypeLookup,
          listTypeLookup,
          areTypesEqual,
        });
        return expectedType ?? InferenceRuleNotApplicable;
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
      ParenthesisedExpr: (node, typir) => {
        const innerType = typir.Inference.inferType(node.expr);
        return Array.isArray(innerType) ? InferenceRuleNotApplicable : innerType;
      },
      
    });

    // Additional validations
    // Return of a function must match the declared return type
    typir.validation.Collector.addValidationRulesForAstNodes({
      DeclFun: (node, accept, typir) => {
        if (!node.returnType) {
          return;
        }

        const declaredReturnType = typir.Inference.inferType(node.returnType);

        if (declaredReturnType !== typeAuto) {
          if (
            !Array.isArray(declaredReturnType) &&
            node.returnExpr.$type === "Record" &&
            recordTypeLookup.has(declaredReturnType)
          ) {
            return;
          }

          typir.validation.Constraints.ensureNodeIsAssignable(
            node.returnExpr,
            node.returnType,
            accept,
            (actual, expected) => ({
              message: `The return type of function ${node.name} is ${userRepr(actual)}, but the declared return type is ${userRepr(expected)}`,
            })
          );
        }
      },

      If: (node, accept, typir) => {
        const conditionType = typir.Inference.inferType(node.condition);
        if (conditionType !== typeAuto) {
        typir.validation.Constraints.ensureNodeIsAssignable(
          node.condition,
          typeBool,
          accept,
          (actual, expected) => ({
            message: `The condition of 'if' must have type ${userRepr(expected)}, but it has type ${userRepr(actual)}`,
          })
        );
        }

        const thenType = typir.Inference.inferType(node.thenExpr);
        const elseType = typir.Inference.inferType(node.elseExpr);
        const expectedType = findExpectedType(node, typir);
        if (
          !Array.isArray(thenType) &&
          thenType &&
          !Array.isArray(elseType) &&
          elseType
        ) {
          if (
            getCompatibleExpressionType(thenType, elseType, typeBottom, areTypesEqual)
          ) {
            return;
          }

          if (
            expectedType &&
            typir.Assignability.isAssignable(thenType, expectedType) &&
            typir.Assignability.isAssignable(elseType, expectedType)
          ) {
            return;
          }
        }

        return typir.validation.Constraints.ensureNodeIsAssignable(
          node.elseExpr,
          node.thenExpr,
          accept,
          (actual, expected) => ({
            message: `The 'else' branch of 'if' must have type ${userRepr(expected)}, but it has type ${userRepr(actual)}`,
          })
        );
      },

      Succ: (node, accept, typir) => {
        const argumentType = typir.Inference.inferType(node.n);
        if (argumentType === typeAuto) {
          return;
        }
        return typir.validation.Constraints.ensureNodeIsAssignable(
          node.n,
          typeNat,
          accept,
          (actual, expected) => ({
            message: `'succ' expects its argument to have type ${userRepr(expected)}, but it has type ${userRepr(actual)}`,
          })
        );
      },

      IsZero: (node, accept, typir) => {
        const argumentType = typir.Inference.inferType(node.n);
        if (argumentType === typeAuto) {
          return;
        }
        return typir.validation.Constraints.ensureNodeIsAssignable(
          node.n,
          typeNat,
          accept,
          (actual, expected) => ({
            message: `'Nat::iszero' expects its argument to have type ${userRepr(expected)}, but it has type ${userRepr(actual)}`,
          })
        );
      },
      Deref: (node, accept, typir) => {
        const referenceType = typir.Inference.inferType(node.expr);
        if (Array.isArray(referenceType)) {
          return;
        }

        if (referenceType === typeAuto) {
          return;
        }

        if (!referenceType || !referenceTypeLookup.has(referenceType)) {
          const actual = referenceType ? userRepr(referenceType) : "unknown";
          accept({
            severity: "error",
            message: `Dereference expects a reference, but the expression has type ${actual}.`,
            languageNode: node.expr,
          });
        }
      },
      Application: (node, accept, typir) => {
        const referencedFunction = getDirectReferencedFunction(node.fun);
        if (referencedFunction) {
          if (referencedFunction.paramDecls.length !== node.args.length) {
            accept({
              severity: "error",
              message: `This function expects ${referencedFunction.paramDecls.length} argument(s), but ${node.args.length} were provided.`,
              languageNode: node,
            });
            return;
          }

          for (let index = 0; index < referencedFunction.paramDecls.length; index++) {
            const expectedType = typir.Inference.inferType(
              referencedFunction.paramDecls[index].paramType
            );
            const actualType = typir.Inference.inferType(node.args[index]);

            if (
              !Array.isArray(expectedType) &&
              expectedType &&
              !Array.isArray(actualType) &&
              actualType &&
              isTypeCompatibleWithAuto(
                actualType,
                expectedType,
                {
                  typeAuto,
                  areTypesEqual,
                  tupleTypeLookup,
                  sumTypeLookup,
                  recordTypeLookup,
                  variantTypeLookup,
                  listTypeLookup,
                  referenceTypeLookup,
                },
                typir
              )
            ) {
              continue;
            }

            typir.validation.Constraints.ensureNodeIsAssignable(
              node.args[index],
              referencedFunction.paramDecls[index].paramType,
              accept,
              (actual, expected) => ({
                message: `Argument ${index + 1} must have type ${userRepr(expected)}, but it has type ${userRepr(actual)}.`,
              })
            );
          }
          return;
        }

        const functionType = getCallableType(node.fun, typir);
        if (!functionType) {
          return;
        }

        if (isAutoType(functionType)) {
          return;
        }

        if (!isFunctionType(functionType)) {
          accept({
            severity: "error",
            message: `Only functions can be applied, but this expression has type ${userRepr(functionType)}.`,
            languageNode: node.fun,
          });
          return;
        }

        const inputs = functionType.getInputs();
        if (inputs.length !== node.args.length) {
          accept({
            severity: "error",
            message: `This function expects ${inputs.length} argument(s), but ${node.args.length} were provided.`,
            languageNode: node,
          });
          return;
        }

        for (let index = 0; index < inputs.length; index++) {
          typir.validation.Constraints.ensureNodeIsAssignable(
            node.args[index],
            inputs[index].type,
            accept,
            (actual, expected) => ({
              message: `Argument ${index + 1} must have type ${userRepr(expected)}, but it has type ${userRepr(actual)}.`,
            })
          );
        }
      },
      TypeApplication: (node, accept) => {
        if (!isVar(node.fun)) {
          return;
        }

        const referencedFunction = getDirectReferencedFunction(node.fun);
        if (referencedFunction?.$type === "DeclFun") {
          accept({
            severity: "error",
            message: "Type arguments can only be applied to generic functions.",
            languageNode: node.fun,
          });
        }
      },
      Assign: (node, accept, typir) => {
        const leftType = typir.Inference.inferType(node.left);
        if (Array.isArray(leftType)) {
          return;
        }

        if (leftType === typeAuto) {
          return;
        }

        const referencedType = leftType
          ? referenceTypeLookup.get(leftType)
          : undefined;
        if (!referencedType) {
          const actual = leftType ? userRepr(leftType) : "unknown";
          accept({
            severity: "error",
            message: `Assignment expects a reference on the left, but the expression has type ${actual}.`,
            languageNode: node.left,
          });
          return;
        }

        typir.validation.Constraints.ensureNodeIsAssignable(
          node.right,
          referencedType,
          accept,
          (actual, expected) => ({
            message: `Assignment expects a value of type ${userRepr(expected)}, but the right-hand side has type ${userRepr(actual)}.`,
          })
        );
      },
      Sequence: (node, accept, typir) => {
        typir.validation.Constraints.ensureNodeIsAssignable(
          node.expr1,
          typeUnit,
          accept,
          (actual, expected) => ({
            message: `The first expression in a sequence must have type ${userRepr(expected)}, but it has type ${userRepr(actual)}.`,
          })
        );
      },
      Throw: (node, accept, typir) => {
        const exceptionType = getDeclaredExceptionType(node, typir);
        if (!exceptionType) {
          if (hasExceptionVariantDeclarations(node)) {
            return;
          }
          accept({
            severity: "error",
            message:
              "No global exception type is declared. Add 'exception type = T' before using throw/try.",
            languageNode: node,
          });
          return;
        }

        if (exceptionType !== typeAuto) {
          typir.validation.Constraints.ensureNodeIsAssignable(
            node.expr,
            exceptionType,
            accept,
            (actual, expected) => ({
              message: `Thrown expressions must have the declared exception type ${userRepr(expected)}, but this expression has type ${userRepr(actual)}.`,
            })
          );
        }
      },
      TryWith: (node, accept, typir) => {
        const exceptionType = getDeclaredExceptionType(node, typir);
        if (!exceptionType) {
          accept({
            severity: "error",
            message:
              "No global exception type is declared. Add 'exception type = T' before using throw/try.",
            languageNode: node,
          });
        }

        const tryType = typir.Inference.inferType(node.tryExpr);
        const fallbackType = typir.Inference.inferType(node.fallbackExpr);
        if (
          Array.isArray(tryType) ||
          Array.isArray(fallbackType) ||
          !tryType ||
          !fallbackType
        ) {
          return;
        }

        if (
          !getCompatibleExpressionType(
            tryType,
            fallbackType,
            typeBottom,
            areTypesEqual
          )
        ) {
          accept({
            severity: "error",
            message: `The try-expression has type ${userRepr(tryType)}, but the fallback has type ${userRepr(fallbackType)}.`,
            languageNode: node.fallbackExpr,
          });
        }
      },
      TryCatch: (node, accept, typir) => {
        const exceptionType = getDeclaredExceptionType(node, typir);
        if (!exceptionType) {
          accept({
            severity: "error",
            message:
              "No global exception type is declared. Add 'exception type = T' before using throw/try.",
            languageNode: node,
          });
          return;
        }

        validateCatchPattern(node.pattern, exceptionType, accept, {
          typeNat,
          typeBool,
          typeUnit,
          userRepr,
          variantTypeLookup,
          sumTypeLookup,
        });

        const tryType = typir.Inference.inferType(node.tryExpr);
        const fallbackType = typir.Inference.inferType(node.fallbackExpr);
        if (
          Array.isArray(tryType) ||
          Array.isArray(fallbackType) ||
          !tryType ||
          !fallbackType
        ) {
          return;
        }

        if (
          !getCompatibleExpressionType(
            tryType,
            fallbackType,
            typeBottom,
            areTypesEqual
          )
        ) {
          accept({
            severity: "error",
            message: `The try-expression has type ${userRepr(tryType)}, but the catch fallback has type ${userRepr(fallbackType)}.`,
            languageNode: node.fallbackExpr,
          });
        }
      },
      Fix: (node, accept, typir) => {
        const functionType = typir.Inference.inferType(node.expr);
        if (Array.isArray(functionType) || !functionType) {
          return;
        }

        if (!isFunctionType(functionType)) {
          accept({
            severity: "error",
            message: `The argument of 'fix' must be a function, but it has type ${userRepr(functionType)}.`,
            languageNode: node.expr,
          });
          return;
        }

        const inputs = functionType.getInputs();
        if (inputs.length !== 1) {
          accept({
            severity: "error",
            message: `'fix' expects a unary function of type T -> T, but this function has ${inputs.length} parameter(s).`,
            languageNode: node.expr,
          });
          return;
        }

        const outputDescriptor = functionType.getOutput("RETURN_UNDEFINED")?.type;
        if (!outputDescriptor) {
          return;
        }

        const resolver = typir.infrastructure.TypeResolver;
        const inputType = resolver.resolve(inputs[0].type);
        const outputType = resolver.resolve(outputDescriptor);

        if (!areTypesEqual(inputType, outputType)) {
          accept({
            severity: "error",
            message: `'fix' expects a function of type T -> T, but this function has type ${userRepr(functionType)}.`,
            languageNode: node.expr,
          });
        }
      },
      ConstMemory: (node, accept, typir) => {
        const inferredType = typir.Inference.inferType(node);
        if (
          Array.isArray(inferredType) ||
          !inferredType ||
          !referenceTypeLookup.has(inferredType)
        ) {
          accept({
            severity: "error",
            message:
              "Cannot infer the referenced type of a memory address literal. Add an annotation like '<0x0> as &T' or use it where a reference type is expected.",
            languageNode: node,
          });
        }
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
            message: `The body of this lambda must have type ${userRepr(expected)}, but it has type ${userRepr(actual)}`,
          })
        );
      },
      TypeTuple: (node, accept) => {
        if (node.types.length < 2) {
          accept({
            severity: "error",
            message: "Tuples must specify at least two component types",
            languageNode: node,
          });
        }
      },
      TypeRecord: (node, accept) => {
        const seen = new Set<string>();
        for (const field of node.fieldTypes) {
          if (seen.has(field.label)) {
            accept({
              severity: "error",
              message: `Record types cannot declare duplicate field '${field.label}'.`,
              languageNode: field,
              languageProperty: "label",
            });
          }
          seen.add(field.label);
        }
      },
      TypeVariant: (node, accept) => {
        const seen = new Set<string>();
        for (const field of node.fieldTypes) {
          if (seen.has(field.label)) {
            accept({
              severity: "error",
              message: `Variant types cannot declare duplicate label '${field.label}'.`,
              languageNode: field,
              languageProperty: "label",
            });
          }
          seen.add(field.label);
        }
      },
      TypeAsc: (node, accept, typir) => {
        return typir.validation.Constraints.ensureNodeIsAssignable(
          node.expr,
          node.type,
          accept,
          (actual, expected) => ({
            message: `An expression annotated with 'as' must have type ${userRepr(expected)}, but it has type ${userRepr(actual)}`,
          })
        );
      },
      Tuple: (node, accept) => {
        if (node.exprs.length < 2) {
          accept({
            severity: "error",
            message: "Tuples must contain at least two expressions",
            languageNode: node,
          });
        }
      },
      Record: (node, accept, typir) => {
        const seen = new Set<string>();
        for (const binding of node.bindings) {
          if (seen.has(binding.name)) {
            accept({
              severity: "error",
              message: `Records cannot contain duplicate field '${binding.name}'.`,
              languageNode: binding,
              languageProperty: "name",
            });
          }
          seen.add(binding.name);
        }

        const expectedRecordType = getExpectedRecordType(
          node,
          typir,
          recordTypeLookup
        );
        if (!expectedRecordType) {
          return;
        }

        const expectedFields = recordTypeLookup.get(expectedRecordType);
        if (!expectedFields) {
          return;
        }

        const actualBindings = new Map(node.bindings.map((binding) => [binding.name, binding]));
        const missingFields = [...expectedFields.keys()].filter(
          (label) => !actualBindings.has(label)
        );
        if (missingFields.length > 0) {
          accept({
            severity: "error",
            code: "ERROR_MISSING_RECORD_FIELDS",
            message: `Missing record field(s): ${missingFields.join(", ")}.`,
            languageNode: node,
          });
        }

        for (const [label, expectedFieldType] of expectedFields) {
          const actualBinding = actualBindings.get(label);
          if (!actualBinding) {
            continue;
          }

          const actualFieldType = typir.Inference.inferType(actualBinding.rhs);
          if (Array.isArray(actualFieldType) || !actualFieldType) {
            continue;
          }

          if (typir.Assignability.isAssignable(actualFieldType, expectedFieldType)) {
            continue;
          }

          accept({
            severity: "error",
            code: "ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION",
            message: `Record field '${label}' expects ${userRepr(expectedFieldType)}, but got ${userRepr(actualFieldType)}.`,
            languageNode: actualBinding.rhs,
          });
        }
      },
      Variant: (node, accept, typir) => {
        const expected = getExpectedVariantType(
          node,
          typir,
          variantTypeLookup,
          referenceTypeLookup
        );
        if (!expected || Array.isArray(expected)) {
          accept({
            severity: "error",
            message:
              "It is not possible to infer the variant type. Add an annotation like 'as <| l: T |>' or use it in the context of an expected type.",
            languageNode: node,
          });
          return;
        }

        const fields = variantTypeLookup.get(expected);
        if (!fields) {
          return;
        }

        if (!fields.has(node.label)) {
          accept({
            severity: "error",
            message: `Variant label '${node.label}' is not present in the expected type.`,
            languageNode: node,
            languageProperty: "label",
          });
          return;
        }

        const expectedType = fields.get(node.label);
        if (expectedType === undefined) {
          if (node.rhs) {
            accept({
              severity: "error",
              message: `Variant label '${node.label}' does not take a value.`,
              languageNode: node,
              languageProperty: "rhs",
            });
          }
          return;
        }

        if (!node.rhs) {
          accept({
            severity: "error",
            message: `Variant label '${node.label}' requires a value of type ${userRepr(expectedType)}.`,
            languageNode: node,
            languageProperty: "label",
          });
          return;
        }

        typir.validation.Constraints.ensureNodeIsAssignable(
          node.rhs,
          expectedType,
          accept,
          (actual, expectedTypeAnnotation) => ({
            message: `Variant label '${node.label}' expects ${userRepr(expectedTypeAnnotation)}, but got ${userRepr(actual)}.`,
          })
        );
      },
      DotTuple: (node, accept, typir) => {
        if (node.index < 1) {
          accept({
            severity: "error",
            message: "Tuple projection indices start at 1",
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
      DotRecord: (node, accept, typir) => {
        const recordType = typir.Inference.inferType(node.expr);
        if (Array.isArray(recordType)) {
          accept({
            severity: "error",
            message:
              "Record projection expects a record, but the expression type could not be inferred.",
            languageNode: node,
            languageProperty: "expr",
          });
          return;
        }

        const fields = recordType ? recordTypeLookup.get(recordType) : undefined;
        if (!fields) {
          const actual = recordType ? userRepr(recordType) : "unknown";
          accept({
            severity: "error",
            message: `Record projection expects a record, but the expression has type ${actual}.`,
            languageNode: node,
            languageProperty: "expr",
          });
          return;
        }

        if (!fields.has(node.label)) {
          accept({
            severity: "error",
            message: `Record has no field named '${node.label}'.`,
            languageNode: node,
            languageProperty: "label",
          });
        }
      },
      NatRec: (node, accept, typir) => {
        const natArgumentType = typir.Inference.inferType(node.n);
        if (natArgumentType !== typeAuto) {
          typir.validation.Constraints.ensureNodeIsAssignable(
            node.n,
            typeNat,
            accept,
            (actual, expected) => ({
              message: `The first argument of 'Nat::rec' must have type ${userRepr(expected)}, but it has type ${userRepr(actual)}`,
            })
          );
        }

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
        if (indexType !== typeNat && indexType !== typeAuto) {
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
        if (
          accumulatorType !== typeAuto &&
          initialType !== typeAuto &&
          !areTypesEqual(accumulatorType, initialType)
        ) {
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

        if (
          finalOutput !== typeAuto &&
          initialType !== typeAuto &&
          !areTypesEqual(finalOutput, initialType)
        ) {
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
          if (
            reference !== typeAuto &&
            current !== typeAuto &&
            !areTypesEqual(reference, current)
          ) {
            accept({
              severity: "error",
              message: `All list elements must have the same type. Expected ${userRepr(reference)}, but element ${
                i + 1
              } has type ${userRepr(current)}.`,
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
            message: `'cons' head must have type ${userRepr(expected)}, but has ${userRepr(actual)}.`,
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
        const expectedSum = getExpectedSumType(
          node,
          typir,
          sumTypeLookup,
          tupleTypeLookup
        );
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
            message: `'inl' expected ${userRepr(expected)}, but get ${userRepr(actual)}`,
          })
        );
      },
      Inr: (node, accept, typir) => {
        const expectedSum = getExpectedSumType(
          node,
          typir,
          sumTypeLookup,
          tupleTypeLookup
        );
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
            message: `'inr' expected ${userRepr(expected)},but get ${userRepr(actual)}`,
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
        const variantFields = variantTypeLookup.get(scrutineeType);
        const autoScrutinee = isAutoType(scrutineeType);

        let inlSeen = false;
        let inrSeen = false;
        const coveredVariantLabels = new Set<string>();
        let variantWildcardSeen = false;
        let boolTrueSeen = false;
        let boolFalseSeen = false;
        let natZeroSeen = false;
        let natPositiveSeen = false;
        let unitSeen = false;
        let listEmptySeen = false;
        let listNonEmptySeen = false;
        let irrefutableSeen = false;

        const branchTypes: TypirType[] = [];
        for (const matchCase of node.cases) {
          if (sumComponents) {
            const coverage = validatePatternAgainstSum(
              matchCase.pattern,
              sumComponents,
              accept,
              typir
            );
            inlSeen ||= coverage.inl;
            inrSeen ||= coverage.inr;
          } else if (variantFields) {
            const coverage = validatePatternAgainstVariant(
              matchCase.pattern,
              variantFields,
              accept,
              typir
            );
            variantWildcardSeen ||= coverage.wildcard;
            for (const label of coverage.labels) {
              coveredVariantLabels.add(label);
            }
          } else if (!autoScrutinee) {
            validatePatternAgainstType(matchCase.pattern, scrutineeType, accept, {
              typeNat,
              typeBool,
              typeUnit,
              userRepr,
              tupleTypeLookup,
              sumTypeLookup,
              recordTypeLookup,
              variantTypeLookup,
              listTypeLookup,
              areTypesEqual,
            });

            irrefutableSeen ||= isIrrefutablePattern(
              matchCase.pattern,
              scrutineeType,
              {
                tupleTypeLookup,
                recordTypeLookup,
                listTypeLookup,
              }
            );

            const boolCoverage = classifyBoolPattern(matchCase.pattern);
            boolTrueSeen ||= boolCoverage === "true" || boolCoverage === "all";
            boolFalseSeen ||= boolCoverage === "false" || boolCoverage === "all";

            const natCoverage = classifyNatPattern(matchCase.pattern);
            natZeroSeen ||= natCoverage === "zero" || natCoverage === "all";
            natPositiveSeen ||=
              natCoverage === "positive" || natCoverage === "all";

            const unitCoverage = classifyUnitPattern(matchCase.pattern);
            unitSeen ||= unitCoverage === "unit" || unitCoverage === "all";

            const listCoverage = classifyListPattern(
              matchCase.pattern,
              scrutineeType,
              {
                listTypeLookup,
                tupleTypeLookup,
                recordTypeLookup,
              }
            );
            listEmptySeen ||= listCoverage === "empty" || listCoverage === "all";
            listNonEmptySeen ||=
              listCoverage === "non-empty" || listCoverage === "all";
          }

          const caseType = typir.Inference.inferType(matchCase.expr);
          if (Array.isArray(caseType) || !caseType) {
            continue;
          }
          branchTypes.push(caseType);
        }

        if (branchTypes.length === node.cases.length) {
          const reference = branchTypes[0];
          const expectedType = findExpectedType(node, typir);
          for (const branchType of branchTypes.slice(1)) {
            if (
              !getCompatibleExpressionType(
                reference,
                branchType,
                typeBottom,
                areTypesEqual
              )
            ) {
              if (
                expectedType &&
                branchTypes.every((type) =>
                  typir.Assignability.isAssignable(type, expectedType)
                )
              ) {
                break;
              }
              accept({
                severity: "error",
                message:
                  "All branches of the 'match' must return the same type.",
                languageNode: node,
              });
              return;
            }
          }
        }

        if (sumComponents) {
          if (!inlSeen || !inrSeen) {
            accept({
              severity: "error",
              message:
                "The total type should be split into both branches: 'inl' and 'inr' are expected.",
              languageNode: node,
            });
          }
        } else if (variantFields && !variantWildcardSeen) {
          const missing = [...variantFields.keys()].filter(
            (label) => !coveredVariantLabels.has(label)
          );
          if (missing.length > 0) {
            accept({
              severity: "error",
              message: `The 'match' must cover all variant labels. Missing: ${missing.join(", ")}.`,
              languageNode: node,
            });
          }
        } else if (!autoScrutinee && areTypesEqual(scrutineeType, typeBool)) {
          if (!boolTrueSeen || !boolFalseSeen) {
            accept({
              severity: "error",
              message:
                "The 'match' over Bool must cover both 'true' and 'false', unless an irrefutable pattern is present.",
              languageNode: node,
            });
          }
        } else if (!autoScrutinee && areTypesEqual(scrutineeType, typeNat)) {
          if (!natZeroSeen || !natPositiveSeen) {
            accept({
              severity: "error",
              message:
                "The 'match' over Nat must cover both zero and successor cases, unless an irrefutable pattern is present.",
              languageNode: node,
            });
          }
        } else if (!autoScrutinee && areTypesEqual(scrutineeType, typeUnit)) {
          if (!unitSeen) {
            accept({
              severity: "error",
              message:
                "The 'match' over Unit must cover 'unit', unless an irrefutable pattern is present.",
              languageNode: node,
            });
          }
        } else if (!autoScrutinee && listTypeLookup.has(scrutineeType)) {
          if (!irrefutableSeen && (!listEmptySeen || !listNonEmptySeen)) {
            accept({
              severity: "error",
              message:
                "The 'match' over lists must cover both the empty and non-empty cases, unless an irrefutable pattern is present.",
              languageNode: node,
            });
          }
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

function findExpectedType(
  node: AstNode,
  typir: TypirServices<StellaSpecifics>
): TypirType | undefined {
  let current: AstNode | undefined = node;
  let container = node.$container as AstNode | undefined;
  if (!container) {
    return undefined;
  }

  while (container) {
    if ((container as { $type?: string; expr?: unknown }).$type === "TypeAsc") {
      const typeAsc = container as { type?: unknown; expr?: unknown };
      if (typeAsc.expr === current && typeAsc.type) {
        const expected = typir.Inference.inferType(typeAsc.type as AstNode);
        if (!Array.isArray(expected) && expected) {
          return expected;
        }
      }
    }

    if (
      isDeclFun(container) &&
      container.returnExpr === current &&
      container.returnType
    ) {
      const expected = typir.Inference.inferType(container.returnType);
      if (!Array.isArray(expected) && expected) {
        return expected;
      }
    }

    if (
      (container as { $type?: string; returnExpr?: unknown }).$type ===
        "Abstraction" &&
      (container as { returnExpr?: unknown }).returnExpr === current
    ) {
      const expectedAbstraction = findExpectedType(container, typir);
      if (
        expectedAbstraction &&
        !Array.isArray(expectedAbstraction) &&
        isFunctionType(expectedAbstraction)
      ) {
        const outputDescriptor =
          expectedAbstraction.getOutput("RETURN_UNDEFINED")?.type;
        if (outputDescriptor) {
          return typir.infrastructure.TypeResolver.resolve(outputDescriptor);
        }
      }
    }

    if (container.$type === Application.$type) {
      const application = container as Application;
      const argIndex = application.args.indexOf(current as never);
      if (argIndex >= 0) {
        const referencedFunction = getDirectReferencedFunction(application.fun);
        const directTypeNode = referencedFunction?.paramDecls[argIndex]?.paramType;
        if (directTypeNode) {
          const directType = typir.Inference.inferType(directTypeNode);
          if (!Array.isArray(directType) && directType) {
            return directType;
          }
        }

        const functionType = getCallableType(application.fun, typir);
        if (functionType && isFunctionType(functionType)) {
          const expectedInput = functionType.getInputs()[argIndex];
          if (expectedInput) {
            return typir.infrastructure.TypeResolver.resolve(expectedInput.type);
          }
        }
      }
    }

    if ((container as MatchCase).expr === current) {
      const matchNode = (container as MatchCase).$container as Match | undefined;
      if (matchNode) {
        const expected = findExpectedType(matchNode, typir);
        if (expected) {
          return expected;
        }
      }
    }

    if (
      (container as { $type?: string; thenExpr?: unknown; elseExpr?: unknown })
        .$type === "If"
    ) {
      const ifNode = container as unknown as {
        thenExpr: AstNode;
        elseExpr: AstNode;
      };
      if (ifNode.thenExpr === current || ifNode.elseExpr === current) {
        const sibling =
          ifNode.thenExpr === current ? ifNode.elseExpr : ifNode.thenExpr;
        const siblingType = typir.Inference.inferType(sibling);
        if (!Array.isArray(siblingType) && siblingType) {
          return siblingType;
        }

        const expected = findExpectedType(container, typir);
        if (expected) {
          return expected;
        }
      }
    }

    current = container;
    container = container.$container as AstNode | undefined;
  }

  return undefined;
}

function getCallableType(
  node: AstNode,
  typir: TypirServices<StellaSpecifics>
): TypirType | undefined {
  const referencedFunction = getDirectReferencedFunction(node);
  if (referencedFunction) {
    const referencedType = typir.Inference.inferType(referencedFunction);
    if (!Array.isArray(referencedType) && referencedType) {
      return referencedType;
    }
  }

  const inferred = typir.Inference.inferType(node);
  return !Array.isArray(inferred) && inferred ? inferred : undefined;
}

function getDirectReferencedFunction(
  node: AstNode
):
  | (AstNode & {
      $type: "DeclFun" | "DeclFunGeneric";
      paramDecls: Array<{ paramType: AstNode }>;
    })
  | undefined {
  if (!isVar(node)) {
    return undefined;
  }

  const referenced = node.ref.ref as AstNode | undefined;
  if (
    referenced &&
    (referenced.$type === "DeclFun" || referenced.$type === "DeclFunGeneric")
  ) {
    return referenced as AstNode & {
      $type: "DeclFun" | "DeclFunGeneric";
      paramDecls: Array<{ paramType: AstNode }>;
    };
  }

  return undefined;
}

function getExpectedSumType(
  node: Inl | Inr,
  typir: TypirServices<StellaSpecifics>,
  sumTypeLookup: Map<TypirType, [TypirType, TypirType]>,
  tupleTypeLookup: Map<TypirType, TypirType[]>
): TypirType | undefined {
  const expected = findExpectedType(node, typir);
  if (expected && sumTypeLookup.has(expected)) {
    return expected;
  }

  const container = node.$container as AstNode | undefined;
  if (!container) {
    return undefined;
  }

  if (
    (container.$type === "Inl" || container.$type === "Inr") &&
    (container as { expr?: AstNode }).expr === node
  ) {
    const outerExpected = getExpectedSumType(
      container as Inl | Inr,
      typir,
      sumTypeLookup,
      tupleTypeLookup
    );
    if (!outerExpected) {
      return undefined;
    }
    const outerComponents = sumTypeLookup.get(outerExpected);
    if (!outerComponents) {
      return undefined;
    }
    return container.$type === "Inl" ? outerComponents[0] : outerComponents[1];
  }

  if (container.$type === "Tuple") {
    const tuple = container as unknown as { exprs: AstNode[] };
    const index = tuple.exprs.indexOf(node as never);
    if (index >= 0) {
      const tupleExpected = findExpectedType(container, typir);
      if (tupleExpected) {
        const components = tupleTypeLookup.get(tupleExpected);
        if (components && index < components.length) {
          return components[index];
        }
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
  const expected = findExpectedType(node, typir);
  return expected && listTypeLookup.has(expected) ? expected : undefined;
}

function getExpectedRecordType(
  node: StellaRecord,
  typir: TypirServices<StellaSpecifics>,
  recordTypeLookup: Map<TypirType, Map<string, TypirType>>
): TypirType | undefined {
  const expected = findExpectedType(node, typir);
  return expected && recordTypeLookup.has(expected) ? expected : undefined;
}

function getExpectedReferenceType(
  node: ConstMemory,
  typir: TypirServices<StellaSpecifics>,
  referenceTypeLookup: Map<TypirType, TypirType>
): TypirType | undefined {
  const expected = findExpectedType(node, typir);
  if (expected && referenceTypeLookup.has(expected)) {
    return expected;
  }

  let current: AstNode | undefined = node;
  let container = node.$container as AstNode | undefined;
  if (!container) return undefined;

  while (container) {
    // Ascription: <0x...> as &T
    if ((container as { $type?: string; expr?: unknown }).$type === "TypeAsc") {
      const typeAsc = container as { type?: unknown; expr?: unknown };
      if (typeAsc.expr === current && typeAsc.type) {
        const expected = typir.Inference.inferType(typeAsc.type as AstNode);
        if (!Array.isArray(expected) && referenceTypeLookup.has(expected)) {
          return expected;
        }
      }
    }

    // Function return position
    if (
      isDeclFun(container) &&
      container.returnExpr === current &&
      container.returnType
    ) {
      const expected = typir.Inference.inferType(container.returnType);
      if (!Array.isArray(expected) && referenceTypeLookup.has(expected)) {
        return expected;
      }
    }

    // Function argument position
    if (container.$type === Application.$type) {
      const application = container as Application;
      const argIndex = application.args.indexOf(current as never);
      if (argIndex >= 0) {
        if (isVar(application.fun)) {
          const declaration = application.fun.ref.ref as DeclFun | undefined;
          const expectedTypeNode = declaration?.paramDecls[argIndex]?.paramType;
          if (expectedTypeNode) {
            const expected = typir.Inference.inferType(expectedTypeNode);
            if (!Array.isArray(expected) && referenceTypeLookup.has(expected)) {
              return expected;
            }
          }
        }

        const functionType = typir.Inference.inferType(application.fun);
        if (
          !Array.isArray(functionType) &&
          functionType &&
          isFunctionType(functionType)
        ) {
          const expectedInput = functionType.getInputs()[argIndex];
          if (expectedInput) {
            const expected = typir.infrastructure.TypeResolver.resolve(
              expectedInput.type
            );
            if (referenceTypeLookup.has(expected)) {
              return expected;
            }
          }
        }
      }
    }

    current = container;
    container = container.$container as AstNode | undefined;
  }

  return undefined;
}

function getDeclaredExceptionType(
  node: AstNode,
  typir: TypirServices<StellaSpecifics>
): TypirType | undefined {
  let root: AstNode = node;
  while (root.$container) {
    root = root.$container as AstNode;
  }

  const program = root as { decls?: AstNode[] };
  if (!program?.decls) {
    return undefined;
  }

  for (const decl of program.decls) {
    if (decl.$type !== "DeclExceptionType") {
      continue;
    }

    const exceptionTypeNode = (decl as unknown as { exceptionType: AstNode })
      .exceptionType;
    const exceptionType = typir.Inference.inferType(exceptionTypeNode);
    if (!Array.isArray(exceptionType) && exceptionType) {
      return exceptionType;
    }
  }

  return undefined;
}

function hasExceptionVariantDeclarations(node: AstNode): boolean {
  let root: AstNode = node;
  while (root.$container) {
    root = root.$container as AstNode;
  }

  const program = root as { decls?: AstNode[] };
  return !!program.decls?.some((decl) => decl.$type === "DeclExceptionVariant");
}

function getCompatibleExpressionType(
  left: TypirType,
  right: TypirType,
  bottom: TypirType,
  areTypesEqual: (left: TypirType, right: TypirType) => boolean
): TypirType | undefined {
  if (areTypesEqual(left, right)) {
    return left;
  }

  if (areTypesEqual(left, bottom)) {
    return right;
  }

  if (areTypesEqual(right, bottom)) {
    return left;
  }

  return undefined;
}

function isTypeCompatibleWithAuto(
  actual: TypirType,
  expected: TypirType,
  helpers: {
    typeAuto: TypirType;
    areTypesEqual: (left: TypirType, right: TypirType) => boolean;
    tupleTypeLookup: Map<TypirType, TypirType[]>;
    sumTypeLookup: Map<TypirType, [TypirType, TypirType]>;
    recordTypeLookup: Map<TypirType, Map<string, TypirType>>;
    variantTypeLookup: Map<TypirType, Map<string, TypirType | undefined>>;
    listTypeLookup: Map<TypirType, TypirType>;
    referenceTypeLookup: Map<TypirType, TypirType>;
  },
  typir: TypirServices<StellaSpecifics>
): boolean {
  if (
    actual === helpers.typeAuto ||
    expected === helpers.typeAuto ||
    helpers.areTypesEqual(actual, expected)
  ) {
    return true;
  }

  const actualTuple = helpers.tupleTypeLookup.get(actual);
  const expectedTuple = helpers.tupleTypeLookup.get(expected);
  if (actualTuple && expectedTuple) {
    return (
      actualTuple.length === expectedTuple.length &&
      actualTuple.every((type, index) =>
        isTypeCompatibleWithAuto(type, expectedTuple[index], helpers, typir)
      )
    );
  }

  const actualSum = helpers.sumTypeLookup.get(actual);
  const expectedSum = helpers.sumTypeLookup.get(expected);
  if (actualSum && expectedSum) {
    return (
      isTypeCompatibleWithAuto(actualSum[0], expectedSum[0], helpers, typir) &&
      isTypeCompatibleWithAuto(actualSum[1], expectedSum[1], helpers, typir)
    );
  }

  const actualRecord = helpers.recordTypeLookup.get(actual);
  const expectedRecord = helpers.recordTypeLookup.get(expected);
  if (actualRecord && expectedRecord) {
    if (actualRecord.size !== expectedRecord.size) {
      return false;
    }
    for (const [label, expectedType] of expectedRecord) {
      const actualType = actualRecord.get(label);
      if (
        !actualType ||
        !isTypeCompatibleWithAuto(actualType, expectedType, helpers, typir)
      ) {
        return false;
      }
    }
    return true;
  }

  const actualVariant = helpers.variantTypeLookup.get(actual);
  const expectedVariant = helpers.variantTypeLookup.get(expected);
  if (actualVariant && expectedVariant) {
    if (actualVariant.size !== expectedVariant.size) {
      return false;
    }
    for (const [label, expectedType] of expectedVariant) {
      if (!actualVariant.has(label)) {
        return false;
      }
      const actualType = actualVariant.get(label);
      if (
        actualType === undefined ||
        expectedType === undefined
          ? actualType !== expectedType
          : !isTypeCompatibleWithAuto(actualType, expectedType, helpers, typir)
      ) {
        return false;
      }
    }
    return true;
  }

  const actualList = helpers.listTypeLookup.get(actual);
  const expectedList = helpers.listTypeLookup.get(expected);
  if (actualList && expectedList) {
    return isTypeCompatibleWithAuto(actualList, expectedList, helpers, typir);
  }

  const actualRef = helpers.referenceTypeLookup.get(actual);
  const expectedRef = helpers.referenceTypeLookup.get(expected);
  if (actualRef && expectedRef) {
    return isTypeCompatibleWithAuto(actualRef, expectedRef, helpers, typir);
  }

  if (isFunctionType(actual) && isFunctionType(expected)) {
    const actualInputs = actual.getInputs();
    const expectedInputs = expected.getInputs();
    if (actualInputs.length !== expectedInputs.length) {
      return false;
    }
    for (let index = 0; index < actualInputs.length; index++) {
      const actualInput = typir.infrastructure.TypeResolver.resolve(
        actualInputs[index].type
      );
      const expectedInput = typir.infrastructure.TypeResolver.resolve(
        expectedInputs[index].type
      );
      if (
        !isTypeCompatibleWithAuto(actualInput, expectedInput, helpers, typir)
      ) {
        return false;
      }
    }

    const actualOutput = actual.getOutput("RETURN_UNDEFINED")?.type;
    const expectedOutput = expected.getOutput("RETURN_UNDEFINED")?.type;
    if (!actualOutput || !expectedOutput) {
      return actualOutput === expectedOutput;
    }

    return isTypeCompatibleWithAuto(
      typir.infrastructure.TypeResolver.resolve(actualOutput),
      typir.infrastructure.TypeResolver.resolve(expectedOutput),
      helpers,
      typir
    );
  }

  return false;
}

function getExpectedPatternType(
  node: AstNode,
  typir: TypirServices<StellaSpecifics>,
  helpers: {
    typeNat: TypirType;
    typeBool: TypirType;
    typeUnit: TypirType;
    tupleTypeLookup: Map<TypirType, TypirType[]>;
    sumTypeLookup: Map<TypirType, [TypirType, TypirType]>;
    recordTypeLookup: Map<TypirType, Map<string, TypirType>>;
    variantTypeLookup: Map<TypirType, Map<string, TypirType | undefined>>;
    listTypeLookup: Map<TypirType, TypirType>;
    areTypesEqual: (left: TypirType, right: TypirType) => boolean;
  }
): TypirType | undefined {
  const binding = AstUtils.getContainerOfType(node, isPatternBinding);
  if (binding) {
    const rhsType = typir.Inference.inferType(binding.rhs);
    if (!Array.isArray(rhsType) && rhsType) {
      return resolveNestedPatternType(binding.pattern, node, rhsType, typir, helpers);
    }
  }

  const matchCase = AstUtils.getContainerOfType(node, isMatchCase);
  if (matchCase) {
    const matchNode = matchCase.$container as Match | undefined;
    if (matchNode) {
      const scrutineeType = typir.Inference.inferType(matchNode.expr);
      if (!Array.isArray(scrutineeType) && scrutineeType) {
        return resolveNestedPatternType(
          matchCase.pattern,
          node,
          scrutineeType,
          typir,
          helpers
        );
      }
    }
  }

  const tryCatch = AstUtils.getContainerOfType(
    node,
    (candidate): candidate is AstNode & {
      $type: "TryCatch";
      pattern: AstNode;
    } => candidate.$type === "TryCatch"
  );
  if (tryCatch?.pattern) {
    const exceptionType = getDeclaredExceptionType(tryCatch, typir);
    if (exceptionType) {
      return resolveNestedPatternType(
        tryCatch.pattern,
        node,
        exceptionType,
        typir,
        helpers
      );
    }
  }

  return undefined;
}

function resolveNestedPatternType(
  current: AstNode,
  target: AstNode,
  expectedType: TypirType,
  typir: TypirServices<StellaSpecifics>,
  helpers: {
    typeNat: TypirType;
    typeBool: TypirType;
    typeUnit: TypirType;
    tupleTypeLookup: Map<TypirType, TypirType[]>;
    sumTypeLookup: Map<TypirType, [TypirType, TypirType]>;
    recordTypeLookup: Map<TypirType, Map<string, TypirType>>;
    variantTypeLookup: Map<TypirType, Map<string, TypirType | undefined>>;
    listTypeLookup: Map<TypirType, TypirType>;
    areTypesEqual: (left: TypirType, right: TypirType) => boolean;
  }
): TypirType | undefined {
  if (current === target) {
    return expectedType;
  }

  if (expectedType.getName() === "auto") {
    switch (current.$type) {
      case "ParenthesisedPattern":
      case "PatternAsc":
      case "PatternCastAs":
      case "PatternInl":
      case "PatternInr":
      case "PatternSucc":
        return resolveNestedPatternType(
          (current as unknown as { pattern: AstNode }).pattern,
          target,
          expectedType,
          typir,
          helpers
        );
      case "PatternVariant": {
        const variantPattern = current as unknown as { pattern?: AstNode };
        return variantPattern.pattern
          ? resolveNestedPatternType(
              variantPattern.pattern,
              target,
              expectedType,
              typir,
              helpers
            )
          : undefined;
      }
      case "PatternTuple":
      case "PatternList": {
        for (const pattern of (current as unknown as { patterns: AstNode[] }).patterns) {
          const nested = resolveNestedPatternType(
            pattern,
            target,
            expectedType,
            typir,
            helpers
          );
          if (nested) {
            return nested;
          }
        }
        return undefined;
      }
      case "PatternRecord": {
        const labelledPatterns = (current as unknown as {
          patterns: Array<{ pattern: AstNode }>;
        }).patterns;
        for (const labelledPattern of labelledPatterns) {
          const nested = resolveNestedPatternType(
            labelledPattern.pattern,
            target,
            expectedType,
            typir,
            helpers
          );
          if (nested) {
            return nested;
          }
        }
        return undefined;
      }
      case "PatternCons": {
        const consPattern = current as unknown as {
          head: AstNode;
          tail: AstNode;
        };
        return (
          resolveNestedPatternType(
            consPattern.head,
            target,
            expectedType,
            typir,
            helpers
          ) ??
          resolveNestedPatternType(
            consPattern.tail,
            target,
            expectedType,
            typir,
            helpers
          )
        );
      }
      default:
        return undefined;
    }
  }

  switch (current.$type) {
    case "ParenthesisedPattern":
      return resolveNestedPatternType(
        (current as unknown as { pattern: AstNode }).pattern,
        target,
        expectedType,
        typir,
        helpers
      );
    case "PatternAsc":
    case "PatternCastAs": {
      const typedPattern = current as unknown as {
        pattern: AstNode;
        type: AstNode;
      };
      const ascribedType = typir.Inference.inferType(typedPattern.type);
      return resolveNestedPatternType(
        typedPattern.pattern,
        target,
        !Array.isArray(ascribedType) && ascribedType ? ascribedType : expectedType,
        typir,
        helpers
      );
    }
    case "PatternInl": {
      const components = helpers.sumTypeLookup.get(expectedType);
      if (!components) {
        return undefined;
      }
      return resolveNestedPatternType(
        (current as unknown as { pattern: AstNode }).pattern,
        target,
        components[0],
        typir,
        helpers
      );
    }
    case "PatternInr": {
      const components = helpers.sumTypeLookup.get(expectedType);
      if (!components) {
        return undefined;
      }
      return resolveNestedPatternType(
        (current as unknown as { pattern: AstNode }).pattern,
        target,
        components[1],
        typir,
        helpers
      );
    }
    case "PatternVariant": {
      const fields = helpers.variantTypeLookup.get(expectedType);
      const variantPattern = current as unknown as {
        label: string;
        pattern?: AstNode;
      };
      const payloadType = fields?.get(variantPattern.label);
      if (!variantPattern.pattern || payloadType === undefined) {
        return undefined;
      }
      return resolveNestedPatternType(
        variantPattern.pattern,
        target,
        payloadType,
        typir,
        helpers
      );
    }
    case "PatternTuple": {
      const components = helpers.tupleTypeLookup.get(expectedType);
      if (!components) {
        return undefined;
      }
      const patterns = (current as unknown as { patterns: AstNode[] }).patterns;
      for (let index = 0; index < Math.min(patterns.length, components.length); index++) {
        const nested = resolveNestedPatternType(
          patterns[index],
          target,
          components[index],
          typir,
          helpers
        );
        if (nested) {
          return nested;
        }
      }
      return undefined;
    }
    case "PatternRecord": {
      const fields = helpers.recordTypeLookup.get(expectedType);
      if (!fields) {
        return undefined;
      }
      const labelledPatterns = (current as unknown as {
        patterns: Array<{ label: string; pattern: AstNode }>;
      }).patterns;
      for (const labelledPattern of labelledPatterns) {
        const fieldType = fields.get(labelledPattern.label);
        if (!fieldType) {
          continue;
        }
        const nested = resolveNestedPatternType(
          labelledPattern.pattern,
          target,
          fieldType,
          typir,
          helpers
        );
        if (nested) {
          return nested;
        }
      }
      return undefined;
    }
    case "PatternList": {
      const elementType = helpers.listTypeLookup.get(expectedType);
      if (!elementType) {
        return undefined;
      }
      for (const pattern of (current as unknown as { patterns: AstNode[] }).patterns) {
        const nested = resolveNestedPatternType(
          pattern,
          target,
          elementType,
          typir,
          helpers
        );
        if (nested) {
          return nested;
        }
      }
      return undefined;
    }
    case "PatternCons": {
      const elementType = helpers.listTypeLookup.get(expectedType);
      if (!elementType) {
        return undefined;
      }
      const consPattern = current as unknown as {
        head: AstNode;
        tail: AstNode;
      };
      return (
        resolveNestedPatternType(
          consPattern.head,
          target,
          elementType,
          typir,
          helpers
        ) ??
        resolveNestedPatternType(
          consPattern.tail,
          target,
          expectedType,
          typir,
          helpers
        )
      );
    }
    case "PatternSucc":
      if (!helpers.areTypesEqual(expectedType, helpers.typeNat)) {
        return undefined;
      }
      return resolveNestedPatternType(
        (current as unknown as { pattern: AstNode }).pattern,
        target,
        expectedType,
        typir,
        helpers
      );
    default:
      return undefined;
  }
}

function validatePatternAgainstType(
  pattern: AstNode,
  expectedType: TypirType,
  accept: (diagnostic: {
    severity: "error" | "warning";
    message: string;
    languageNode: AstNode;
  }) => void,
  helpers: {
    typeNat: TypirType;
    typeBool: TypirType;
    typeUnit: TypirType;
    userRepr: (type: TypirType) => string;
    tupleTypeLookup: Map<TypirType, TypirType[]>;
    sumTypeLookup: Map<TypirType, [TypirType, TypirType]>;
    recordTypeLookup: Map<TypirType, Map<string, TypirType>>;
    variantTypeLookup: Map<TypirType, Map<string, TypirType | undefined>>;
    listTypeLookup: Map<TypirType, TypirType>;
    areTypesEqual: (left: TypirType, right: TypirType) => boolean;
  }
): void {
  if (expectedType.getName() === "auto") {
    return;
  }

  switch (pattern.$type) {
    case "PatternVar":
      return;
    case "ParenthesisedPattern":
      validatePatternAgainstType(
        (pattern as unknown as { pattern: AstNode }).pattern,
        expectedType,
        accept,
        helpers
      );
      return;
    case "PatternAsc":
    case "PatternCastAs":
      validatePatternAgainstType(
        (pattern as unknown as { pattern: AstNode }).pattern,
        expectedType,
        accept,
        helpers
      );
      return;
    case "PatternTrue":
    case "PatternFalse":
      if (!helpers.areTypesEqual(expectedType, helpers.typeBool)) {
        accept({
          severity: "error",
          message: `This pattern expects Bool, but the scrutinee has type ${helpers.userRepr(expectedType)}.`,
          languageNode: pattern,
        });
      }
      return;
    case "PatternUnit":
      if (!helpers.areTypesEqual(expectedType, helpers.typeUnit)) {
        accept({
          severity: "error",
          message: `This pattern expects Unit, but the scrutinee has type ${helpers.userRepr(expectedType)}.`,
          languageNode: pattern,
        });
      }
      return;
    case "PatternInt":
      if (!helpers.areTypesEqual(expectedType, helpers.typeNat)) {
        accept({
          severity: "error",
          message: `This pattern expects Nat, but the scrutinee has type ${helpers.userRepr(expectedType)}.`,
          languageNode: pattern,
        });
      }
      return;
    case "PatternSucc":
      if (!helpers.areTypesEqual(expectedType, helpers.typeNat)) {
        accept({
          severity: "error",
          message: `The 'succ' pattern expects Nat, but the scrutinee has type ${helpers.userRepr(expectedType)}.`,
          languageNode: pattern,
        });
        return;
      }
      validatePatternAgainstType(
        (pattern as unknown as { pattern: AstNode }).pattern,
        expectedType,
        accept,
        helpers
      );
      return;
    case "PatternInl":
    case "PatternInr": {
      const components = helpers.sumTypeLookup.get(expectedType);
      if (!components) {
        accept({
          severity: "error",
          message: `This pattern expects a sum type, but the scrutinee has type ${helpers.userRepr(expectedType)}.`,
          languageNode: pattern,
        });
        return;
      }
      const innerExpected =
        pattern.$type === "PatternInl" ? components[0] : components[1];
      validatePatternAgainstType(
        (pattern as unknown as { pattern: AstNode }).pattern,
        innerExpected,
        accept,
        helpers
      );
      return;
    }
    case "PatternVariant": {
      const fields = helpers.variantTypeLookup.get(expectedType);
      if (!fields) {
        accept({
          severity: "error",
          message: `This pattern expects a variant type, but the scrutinee has type ${helpers.userRepr(expectedType)}.`,
          languageNode: pattern,
        });
        return;
      }
      const variantPattern = pattern as unknown as {
        label: string;
        pattern?: AstNode;
      };
      if (!fields.has(variantPattern.label)) {
        accept({
          severity: "error",
          message: `Variant label '${variantPattern.label}' is not present in the scrutinee type.`,
          languageNode: pattern,
        });
        return;
      }
      const payloadType = fields.get(variantPattern.label);
      if (variantPattern.pattern && payloadType !== undefined) {
        validatePatternAgainstType(
          variantPattern.pattern,
          payloadType,
          accept,
          helpers
        );
      }
      return;
    }
    case "PatternTuple": {
      const components = helpers.tupleTypeLookup.get(expectedType);
      const patterns = (pattern as unknown as { patterns: AstNode[] }).patterns;
      if (!components) {
        accept({
          severity: "error",
          message: `This pattern expects a tuple, but the scrutinee has type ${helpers.userRepr(expectedType)}.`,
          languageNode: pattern,
        });
        return;
      }
      if (components.length !== patterns.length) {
        accept({
          severity: "error",
          message: `This tuple pattern has ${patterns.length} element(s), but the scrutinee tuple has ${components.length}.`,
          languageNode: pattern,
        });
        return;
      }
      for (let index = 0; index < patterns.length; index++) {
        validatePatternAgainstType(
          patterns[index],
          components[index],
          accept,
          helpers
        );
      }
      return;
    }
    case "PatternRecord": {
      const fields = helpers.recordTypeLookup.get(expectedType);
      const labelledPatterns = (pattern as unknown as {
        patterns: Array<{ label: string; pattern: AstNode }>;
      }).patterns;
      if (!fields) {
        accept({
          severity: "error",
          message: `This pattern expects a record, but the scrutinee has type ${helpers.userRepr(expectedType)}.`,
          languageNode: pattern,
        });
        return;
      }

      const labels = labelledPatterns.map((item) => item.label);
      if (
        labelledPatterns.length !== fields.size ||
        labels.some((label) => !fields.has(label))
      ) {
        accept({
          severity: "error",
          message: "Record patterns must mention exactly the fields of the scrutinee type.",
          languageNode: pattern,
        });
        return;
      }

      for (const labelledPattern of labelledPatterns) {
        const fieldType = fields.get(labelledPattern.label);
        if (!fieldType) {
          continue;
        }
        validatePatternAgainstType(
          labelledPattern.pattern,
          fieldType,
          accept,
          helpers
        );
      }
      return;
    }
    case "PatternList": {
      const elementType = helpers.listTypeLookup.get(expectedType);
      if (!elementType) {
        accept({
          severity: "error",
          message: `This pattern expects a list, but the scrutinee has type ${helpers.userRepr(expectedType)}.`,
          languageNode: pattern,
        });
        return;
      }
      for (const item of (pattern as unknown as { patterns: AstNode[] }).patterns) {
        validatePatternAgainstType(item, elementType, accept, helpers);
      }
      return;
    }
    case "PatternCons": {
      const elementType = helpers.listTypeLookup.get(expectedType);
      if (!elementType) {
        accept({
          severity: "error",
          message: `This pattern expects a list, but the scrutinee has type ${helpers.userRepr(expectedType)}.`,
          languageNode: pattern,
        });
        return;
      }
      const consPattern = pattern as unknown as {
        head: AstNode;
        tail: AstNode;
      };
      validatePatternAgainstType(consPattern.head, elementType, accept, helpers);
      validatePatternAgainstType(consPattern.tail, expectedType, accept, helpers);
      return;
    }
    default:
      accept({
        severity: "error",
        message: `This pattern is not compatible with ${helpers.userRepr(expectedType)}.`,
        languageNode: pattern,
      });
  }
}

function isIrrefutablePattern(
  pattern: AstNode,
  expectedType: TypirType,
  helpers: {
    tupleTypeLookup: Map<TypirType, TypirType[]>;
    recordTypeLookup: Map<TypirType, Map<string, TypirType>>;
    listTypeLookup: Map<TypirType, TypirType>;
  }
): boolean {
  switch (pattern.$type) {
    case "PatternVar":
      return true;
    case "ParenthesisedPattern":
    case "PatternAsc":
    case "PatternCastAs":
      return isIrrefutablePattern(
        (pattern as unknown as { pattern: AstNode }).pattern,
        expectedType,
        helpers
      );
    case "PatternTuple": {
      const components = helpers.tupleTypeLookup.get(expectedType);
      const patterns = (pattern as unknown as { patterns: AstNode[] }).patterns;
      return (
        !!components &&
        components.length === patterns.length &&
        patterns.every((item, index) =>
          isIrrefutablePattern(item, components[index], helpers)
        )
      );
    }
    case "PatternRecord": {
      const fields = helpers.recordTypeLookup.get(expectedType);
      const labelledPatterns = (pattern as unknown as {
        patterns: Array<{ label: string; pattern: AstNode }>;
      }).patterns;
      return (
        !!fields &&
        labelledPatterns.length === fields.size &&
        labelledPatterns.every(
          (item) =>
            fields.has(item.label) &&
            isIrrefutablePattern(item.pattern, fields.get(item.label)!, helpers)
        )
      );
    }
    case "PatternCons": {
      const consPattern = pattern as unknown as {
        head: AstNode;
        tail: AstNode;
      };
      const elementType = helpers.listTypeLookup.get(expectedType);
      return (
        !!elementType &&
        isIrrefutablePattern(consPattern.head, elementType, helpers) &&
        isIrrefutablePattern(consPattern.tail, expectedType, helpers)
      );
    }
    default:
      return false;
  }
}

function classifyBoolPattern(
  pattern: AstNode
): "true" | "false" | "all" | undefined {
  switch (pattern.$type) {
    case "PatternVar":
      return "all";
    case "ParenthesisedPattern":
    case "PatternAsc":
    case "PatternCastAs":
      return classifyBoolPattern(
        (pattern as unknown as { pattern: AstNode }).pattern
      );
    case "PatternTrue":
      return "true";
    case "PatternFalse":
      return "false";
    default:
      return undefined;
  }
}

function classifyNatPattern(
  pattern: AstNode
): "zero" | "positive" | "all" | undefined {
  switch (pattern.$type) {
    case "PatternVar":
      return "all";
    case "ParenthesisedPattern":
    case "PatternAsc":
    case "PatternCastAs":
      return classifyNatPattern(
        (pattern as unknown as { pattern: AstNode }).pattern
      );
    case "PatternInt":
      return (pattern as unknown as { n: number }).n === 0
        ? "zero"
        : "positive";
    case "PatternSucc":
      return "positive";
    default:
      return undefined;
  }
}

function classifyUnitPattern(
  pattern: AstNode
): "unit" | "all" | undefined {
  switch (pattern.$type) {
    case "PatternVar":
      return "all";
    case "ParenthesisedPattern":
    case "PatternAsc":
    case "PatternCastAs":
      return classifyUnitPattern(
        (pattern as unknown as { pattern: AstNode }).pattern
      );
    case "PatternUnit":
      return "unit";
    default:
      return undefined;
  }
}

function classifyListPattern(
  pattern: AstNode,
  expectedType: TypirType,
  helpers: {
    listTypeLookup: Map<TypirType, TypirType>;
    tupleTypeLookup: Map<TypirType, TypirType[]>;
    recordTypeLookup: Map<TypirType, Map<string, TypirType>>;
  }
): "empty" | "non-empty" | "all" | undefined {
  switch (pattern.$type) {
    case "PatternVar":
      return "all";
    case "ParenthesisedPattern":
    case "PatternAsc":
    case "PatternCastAs":
      return classifyListPattern(
        (pattern as unknown as { pattern: AstNode }).pattern,
        expectedType,
        helpers
      );
    case "PatternList":
      return (pattern as unknown as { patterns: AstNode[] }).patterns.length === 0
        ? "empty"
        : undefined;
    case "PatternCons": {
      const elementType = helpers.listTypeLookup.get(expectedType);
      if (!elementType) {
        return undefined;
      }
      const consPattern = pattern as unknown as {
        head: AstNode;
        tail: AstNode;
      };
      return isIrrefutablePattern(consPattern.head, elementType, helpers) &&
        isIrrefutablePattern(consPattern.tail, expectedType, helpers)
        ? "non-empty"
        : undefined;
    }
    default:
      return undefined;
  }
}

function validateCatchPattern(
  pattern: AstNode,
  expectedType: TypirType,
  accept: (diagnostic: {
    severity: "error" | "warning";
    message: string;
    languageNode: AstNode;
  }) => void,
  helpers: {
    typeNat: TypirType;
    typeBool: TypirType;
    typeUnit: TypirType;
    userRepr: (type: TypirType) => string;
    variantTypeLookup: Map<TypirType, Map<string, TypirType | undefined>>;
    sumTypeLookup: Map<TypirType, [TypirType, TypirType]>;
  }
): void {
  switch (pattern.$type) {
    case "PatternVar":
      return;
    case "PatternInt":
      if (expectedType !== helpers.typeNat) {
        accept({
          severity: "error",
          message: `This catch pattern expects ${helpers.userRepr(helpers.typeNat)}, but the declared exception type is ${helpers.userRepr(expectedType)}.`,
          languageNode: pattern,
        });
      }
      return;
    case "PatternTrue":
    case "PatternFalse":
      if (expectedType !== helpers.typeBool) {
        accept({
          severity: "error",
          message: `This catch pattern expects ${helpers.userRepr(helpers.typeBool)}, but the declared exception type is ${helpers.userRepr(expectedType)}.`,
          languageNode: pattern,
        });
      }
      return;
    case "PatternUnit":
      if (expectedType !== helpers.typeUnit) {
        accept({
          severity: "error",
          message: `This catch pattern expects ${helpers.userRepr(helpers.typeUnit)}, but the declared exception type is ${helpers.userRepr(expectedType)}.`,
          languageNode: pattern,
        });
      }
      return;
    case "PatternInl": {
      const components = helpers.sumTypeLookup.get(expectedType);
      if (!components) {
        accept({
          severity: "error",
          message: `The catch pattern 'inl' expects a sum exception type, but the declared exception type is ${helpers.userRepr(expectedType)}.`,
          languageNode: pattern,
        });
        return;
      }

      validateCatchPattern(
        (pattern as PatternInl).pattern,
        components[0],
        accept,
        helpers
      );
      return;
    }
    case "PatternInr": {
      const components = helpers.sumTypeLookup.get(expectedType);
      if (!components) {
        accept({
          severity: "error",
          message: `The catch pattern 'inr' expects a sum exception type, but the declared exception type is ${helpers.userRepr(expectedType)}.`,
          languageNode: pattern,
        });
        return;
      }

      validateCatchPattern(
        (pattern as PatternInr).pattern,
        components[1],
        accept,
        helpers
      );
      return;
    }
    case "PatternVariant": {
      const fields = helpers.variantTypeLookup.get(expectedType);
      if (!fields) {
        accept({
          severity: "error",
          message: `This catch pattern expects a variant exception type, but the declared exception type is ${helpers.userRepr(expectedType)}.`,
          languageNode: pattern,
        });
        return;
      }

      const variantPattern = pattern as PatternVariant;
      if (!fields.has(variantPattern.label)) {
        accept({
          severity: "error",
          message: `Exception pattern label '${variantPattern.label}' is not present in the declared exception type.`,
          languageNode: pattern,
        });
        return;
      }

      const payloadType = fields.get(variantPattern.label);
      if (!variantPattern.pattern || !payloadType) {
        return;
      }

      validateCatchPattern(variantPattern.pattern, payloadType, accept, helpers);
      return;
    }
    default:
      accept({
        severity: "error",
        message:
          "This catch pattern form is not supported by the current exception type checker implementation.",
        languageNode: pattern,
      });
  }
}

function getExpectedVariantType(
  node: Variant,
  typir: TypirServices<StellaSpecifics>,
  variantTypeLookup: Map<TypirType, Map<string, TypirType | undefined>>,
  referenceTypeLookup: Map<TypirType, TypirType>
): TypirType | undefined {
  const expected = findExpectedType(node, typir);
  if (expected && variantTypeLookup.has(expected)) {
    return expected;
  }

  const container = node.$container as AstNode | undefined;
  if (
    container?.$type === "Ref" &&
    (container as { expr?: AstNode }).expr === node
  ) {
    const expectedReference = findExpectedType(container, typir);
    if (expectedReference) {
      const referencedType = referenceTypeLookup.get(expectedReference);
      if (referencedType && variantTypeLookup.has(referencedType)) {
        return referencedType;
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

function validatePatternAgainstVariant(
  pattern: PatternVariant | PatternVar | AstNode,
  variantFields: Map<string, TypirType | undefined>,
  accept: (diagnostic: {
    severity: "error" | "warning";
    message: string;
    languageNode: AstNode;
  }) => void,
  typir: TypirServices<StellaSpecifics>
): { labels: Set<string>; wildcard: boolean } {
  switch ((pattern as AstNode).$type) {
    case "PatternVariant": {
      const variantPattern = pattern as PatternVariant;
      if (!variantFields.has(variantPattern.label)) {
        accept({
          severity: "error",
          message: `Variant pattern label '${variantPattern.label}' is not present in the scrutinee type.`,
          languageNode: variantPattern,
        });
        return { labels: new Set(), wildcard: false };
      }

      const expectedType = variantFields.get(variantPattern.label);
      if (expectedType === undefined) {
        if (variantPattern.pattern) {
          accept({
            severity: "error",
            message: `Variant label '${variantPattern.label}' is nullary and does not accept a pattern.`,
            languageNode: variantPattern,
          });
        }
      } else {
        if (!variantPattern.pattern) {
          accept({
            severity: "error",
            message: `Variant label '${variantPattern.label}' requires a pattern.`,
            languageNode: variantPattern,
          });
        } else if (variantPattern.pattern.$type !== "PatternVar") {
          const innerType = typir.Inference.inferType(
            variantPattern.pattern as AstNode
          );
          if (
            innerType &&
            !Array.isArray(innerType) &&
            !typir.Equality.getTypeEqualityProblem(innerType, expectedType)
          ) {
            // ok
          } else if (innerType && !Array.isArray(innerType)) {
            accept({
              severity: "error",
              message: `Variant label '${variantPattern.label}' expects a value of type ${expectedType.getName()}.`,
              languageNode: variantPattern.pattern as AstNode,
            });
          }
        }
      }

      return { labels: new Set([variantPattern.label]), wildcard: false };
    }
    case "PatternVar":
      return { labels: new Set(), wildcard: true };
    default:
      accept({
        severity: "error",
        message:
          "For variant matching, only variant patterns or variables are acceptable.",
        languageNode: pattern as AstNode,
      });
      return { labels: new Set(), wildcard: false };
  }
}
