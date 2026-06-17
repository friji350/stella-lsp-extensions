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
  PatternInl,
  PatternInr, 
  PatternVar,
  List,

  isPatternBinding,
} from "../generated/ast.js";
import { Extensions, getExtensions } from "../extensions.js";

export interface StellaSpecifics extends TypirLangiumSpecifics {
  AstTypes: StellaAstType;
}

export type TypirStellaServices = TypirLangiumServices<StellaSpecifics>;

interface StellaTypeContext {
  typir: TypirServices<StellaSpecifics>;
  typeAuto: TypirType;
  typeTop: TypirType;
  typeBottom: TypirType;
  areTypesEqual: (left: TypirType, right: TypirType) => boolean;
  tupleTypeLookup: Map<TypirType, TypirType[]>;
  sumTypeLookup: Map<TypirType, [TypirType, TypirType]>;
  recordTypeLookup: Map<TypirType, Map<string, TypirType>>;
  variantTypeLookup: Map<TypirType, Map<string, TypirType | undefined>>;
  listTypeLookup: Map<TypirType, TypirType>;
  referenceTypeLookup: Map<TypirType, TypirType>;
  forallTypeLookup: Map<TypirType, { params: TypirType[]; body: TypirType }>;
  typeVariableLookup: Map<TypirType, AstNode>;
  substituteType: (
    type: TypirType,
    substitutions: Map<TypirType, TypirType>
  ) => TypirType;
}

type ExpectedTypeMode = "full" | "nonInferenceDriven" | "container" | "direct";

export class StellaTypeSystem
  implements LangiumTypeSystemDefinition<StellaSpecifics>
{
  onInitialize(typir: TypirStellaServices): void {
    const typeNat = typir.factory.Primitives.create({
      primitiveName: "Nat",
    })
      .inferenceRule({ languageKey: ConstInt.$type })
      .inferenceRule({ languageKey: TypeNat.$type }) 
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
      let program: AstNode = node;
      while (program.$container) {
        program = program.$container as AstNode;
      }
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
    let typeContext: StellaTypeContext;

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
    const typeVariableCache = new WeakMap<AstNode, TypirType>();
    const typeVariableLookup = new Map<TypirType, AstNode>();
    const forallTypeCache = new Map<string, TypirType>();
    const forallTypeLookup = new Map<
      TypirType,
      { params: TypirType[]; body: TypirType }
    >();
    const astNodeIds = new WeakMap<AstNode, number>();
    let nextAstNodeId = 1;

    const getAstNodeId = (node: AstNode): number => {
      const existing = astNodeIds.get(node);
      if (existing) {
        return existing;
      }
      const created = nextAstNodeId++;
      astNodeIds.set(node, created);
      return created;
    };

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

    const getOrCreateTypeVariableType = (
      generic: AstNode & { name?: string }
    ): TypirType => {
      const cached = typeVariableCache.get(generic);
      if (cached) {
        return cached;
      }

      const name = generic.name ?? "_";
      const typeVariable = typir.factory.Primitives.create({
        primitiveName: `TypeVar<${name}>#${getAstNodeId(generic)}`,
        associatedLanguageNode: generic,
      }).finish();
      typeVariableCache.set(generic, typeVariable);
      typeVariableLookup.set(typeVariable, generic);
      return typeVariable;
    };

    const forallTypeKey = (params: TypirType[], body: TypirType) =>
      `${params.map((type) => type.getIdentifier()).join(",")}.${body.getIdentifier()}`;

    const forallPrimitiveName = (params: TypirType[], body: TypirType) =>
      `ForAll<${params
        .map((type) => typir.Printer.printTypeName(type))
        .join(", ")} . ${typir.Printer.printTypeName(body)}>`;

    const getOrCreateForallType = (
      params: TypirType[],
      body: TypirType,
      associatedLanguageNode?: AstNode
    ): TypirType => {
      const key = forallTypeKey(params, body);
      const cached = forallTypeCache.get(key);
      if (cached) {
        return cached;
      }

      const forallType = typir.factory.Primitives.create({
        primitiveName: `${forallPrimitiveName(params, body)}#${key}`,
        associatedLanguageNode,
      }).finish();
      forallTypeCache.set(key, forallType);
      forallTypeLookup.set(forallType, { params: params.slice(), body });
      return forallType;
    };

    const substituteType = (
      type: TypirType,
      substitutions: Map<TypirType, TypirType>
    ): TypirType => {
      const direct = substitutions.get(type);
      if (direct) {
        return direct;
      }

      const tupleComponents = tupleTypeLookup.get(type);
      if (tupleComponents) {
        return getOrCreateTupleType(
          tupleComponents.map((component) =>
            substituteType(component, substitutions)
          )
        );
      }

      const sumComponents = sumTypeLookup.get(type);
      if (sumComponents) {
        return getOrCreateSumType(
          substituteType(sumComponents[0], substitutions),
          substituteType(sumComponents[1], substitutions)
        );
      }

      const recordFields = recordTypeLookup.get(type);
      if (recordFields) {
        return getOrCreateRecordType(
          [...recordFields.entries()].map(([label, fieldType]) => ({
            label,
            type: substituteType(fieldType, substitutions),
          }))
        );
      }

      const variantFields = variantTypeLookup.get(type);
      if (variantFields) {
        return getOrCreateVariantType(
          [...variantFields.entries()].map(([label, payload]) => ({
            label,
            type: payload ? substituteType(payload, substitutions) : undefined,
          }))
        );
      }

      const listElement = listTypeLookup.get(type);
      if (listElement) {
        return getOrCreateListType(substituteType(listElement, substitutions));
      }

      const referenced = referenceTypeLookup.get(type);
      if (referenced) {
        return getOrCreateReferenceType(substituteType(referenced, substitutions));
      }

      const forall = forallTypeLookup.get(type);
      if (forall) {
        const nestedSubstitutions = new Map(substitutions);
        for (const param of forall.params) {
          nestedSubstitutions.delete(param);
        }
        return getOrCreateForallType(
          forall.params,
          substituteType(forall.body, nestedSubstitutions)
        );
      }

      if (isFunctionType(type)) {
        const output = type.getOutput("RETURN_UNDEFINED")?.type;
        if (!output) {
          return type;
        }

        return getOrCreateFunctionType(
          type.getInputs().map((input) =>
            substituteType(
              typir.infrastructure.TypeResolver.resolve(input.type),
              substitutions
            )
          ),
          substituteType(
            typir.infrastructure.TypeResolver.resolve(output),
            substitutions
          )
        );
      }

      return type;
    };

    const getDirectFunctionValueType = (node: AstNode): TypirType | undefined => {
      const referencedFunction = getDirectReferencedFunction(node);
      if (!referencedFunction?.returnType) {
        return undefined;
      }

      const paramTypes: TypirType[] = [];
      for (const param of referencedFunction.paramDecls) {
        const paramType = typir.Inference.inferType(param.paramType);
        if (Array.isArray(paramType) || !paramType) {
          return undefined;
        }
        paramTypes.push(paramType);
      }

      const returnType = typir.Inference.inferType(referencedFunction.returnType);
      if (Array.isArray(returnType) || !returnType) {
        return undefined;
      }

      return getOrCreateFunctionType(paramTypes, returnType, referencedFunction);
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
    const isKnownAssignable = (
      source: TypirType,
      target: TypirType
    ): boolean => isStructurallyAssignable(source, target, typeContext);
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
          isKnownAssignable(component, otherComponents[index])
        );
        if (candidateIsSubtype) {
          markSubtypeIf(candidate, otherType);
        }

        const otherIsSubtype = otherComponents.every((component, index) =>
          isKnownAssignable(component, candidateComponents[index])
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
          isKnownAssignable(candidateComponents[0], otherComponents[0]) &&
          isKnownAssignable(candidateComponents[1], otherComponents[1]);
        if (candidateIsSubtype) {
          markSubtypeIf(candidate, otherType);
        }

        const otherIsSubtype =
          isKnownAssignable(otherComponents[0], candidateComponents[0]) &&
          isKnownAssignable(otherComponents[1], candidateComponents[1]);
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
              isKnownAssignable(candidateFieldType, otherFieldType)
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
              isKnownAssignable(otherFieldType, candidateFieldType)
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

            return isKnownAssignable(candidatePayload, otherPayload);
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

            return isKnownAssignable(otherPayload, candidatePayload);
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
        if (isKnownAssignable(candidateElementType, otherElementType)) {
          markSubtypeIf(candidate, otherType);
        }
        if (isKnownAssignable(otherElementType, candidateElementType)) {
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
          isKnownAssignable(candidateReferencedType, otherReferencedType) &&
          isKnownAssignable(otherReferencedType, candidateReferencedType);
        if (candidateIsSubtype) {
          markSubtypeIf(candidate, otherType);
        }

        const otherIsSubtype =
          isKnownAssignable(otherReferencedType, candidateReferencedType) &&
          isKnownAssignable(candidateReferencedType, otherReferencedType);
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
          isKnownAssignable(candidateOutput.type, otherOutput.type) &&
          candidateInputs.every((candidateInput, index) =>
            isKnownAssignable(
              otherInputs[index].type,
              candidateInput.type
            )
          );
        if (candidateIsSubtype) {
          markSubtypeIf(candidate, otherType);
        }

        const otherIsSubtype =
          isKnownAssignable(otherOutput.type, candidateOutput.type) &&
          otherInputs.every((otherInput, index) =>
            isKnownAssignable(
              candidateInputs[index].type,
              otherInput.type
            )
          );
        if (otherIsSubtype) {
          markSubtypeIf(otherType, candidate);
        }
      }
    };
    

    const typeTop = typir.factory.Top.create({})
      .inferenceRule({ languageKey: TypeTop.$type })
      .finish();

    const typeBottom = typir.factory.Bottom.create({})
      .inferenceRule({ languageKey: TypeBottom.$type })
      .finish();

    typeContext = {
      typir,
      typeAuto,
      typeTop,
      typeBottom,
      areTypesEqual,
      tupleTypeLookup,
      sumTypeLookup,
      recordTypeLookup,
      variantTypeLookup,
      listTypeLookup,
      referenceTypeLookup,
      forallTypeLookup,
      typeVariableLookup,
      substituteType,
    };

    registerAutoCompatibility(typeNat);
    registerAutoCompatibility(typeBool);
    registerAutoCompatibility(typeUnit);
    registerAutoCompatibility(typeTop);
    registerAutoCompatibility(typeBottom);

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

    typir.Inference.addInferenceRulesForAstNodes({
      Var: (node) => node.ref.ref ?? InferenceRuleNotApplicable, 
      DeclFunGeneric: (node, typir) => {
        const paramTypes: TypirType[] = [];
        for (const param of node.paramDecls) {
          const paramType = typir.Inference.inferType(param.paramType);
          if (Array.isArray(paramType) || !paramType) {
            return InferenceRuleNotApplicable;
          }
          paramTypes.push(paramType);
        }

        if (!node.returnType) {
          return InferenceRuleNotApplicable;
        }
        const returnType = typir.Inference.inferType(node.returnType);
        if (Array.isArray(returnType) || !returnType) {
          return InferenceRuleNotApplicable;
        }

        return getOrCreateForallType(
          node.generics.map((generic) => getOrCreateTypeVariableType(generic)),
          getOrCreateFunctionType(paramTypes, returnType, node),
          node
        );
      },
      Application: (node, typir) => {
        if (isVar(node.fun)) {
          const referenced = node.fun.ref.ref as
            | (AstNode & {
                $type: "DeclFun";
                returnType?: AstNode;
                returnExpr?: AstNode;
              })
            | undefined;
          if (
            referenced?.$type === "DeclFun" &&
            referenced.returnExpr?.$type === "Abstraction"
          ) {
            const actualReturnType = typir.Inference.inferType(referenced.returnExpr);
            if (!Array.isArray(actualReturnType) && actualReturnType) {
              return actualReturnType;
            }
          }
          if (referenced?.$type === "DeclFun" && referenced.returnType) {
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
      TypeVar: (node) => {
        const referenced = node.ref.ref as AstNode | undefined;
        return referenced?.$type === "GenericTypeVar"
          ? getOrCreateTypeVariableType(referenced as AstNode & { name?: string })
          : InferenceRuleNotApplicable;
      },
      TypeForAll: (node, typir) => {
        const bodyType = typir.Inference.inferType(node.type);
        if (Array.isArray(bodyType) || !bodyType) {
          return InferenceRuleNotApplicable;
        }

        return getOrCreateForallType(
          node.types.map((generic) => getOrCreateTypeVariableType(generic)),
          bodyType,
          node
        );
      },
      TypeAbstraction: (node, typir) => {
        const bodyType = typir.Inference.inferType(node.expr);
        if (Array.isArray(bodyType) || !bodyType) {
          return InferenceRuleNotApplicable;
        }

        return getOrCreateForallType(
          node.generics.map((generic) => getOrCreateTypeVariableType(generic)),
          bodyType,
          node
        );
      },
      TypeApplication: (node, typir) => {
        const genericType = typir.Inference.inferType(node.fun);
        if (Array.isArray(genericType) || !genericType) {
          return InferenceRuleNotApplicable;
        }

        const forall = forallTypeLookup.get(genericType);
        if (!forall || forall.params.length !== node.types.length) {
          return InferenceRuleNotApplicable;
        }

        const substitutions = new Map<TypirType, TypirType>();
        for (let index = 0; index < forall.params.length; index++) {
          const argumentType = typir.Inference.inferType(node.types[index]);
          if (Array.isArray(argumentType) || !argumentType) {
            return InferenceRuleNotApplicable;
          }
          substitutions.set(forall.params[index], argumentType);
        }

        return substituteType(forall.body, substitutions);
      },
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
        const expected = getExpectedVariantType(node, typeContext);
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
            areTypesEqual,
            isKnownAssignable
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
            areTypesEqual,
            isKnownAssignable
          ) ?? InferenceRuleNotApplicable
        );
      },
      TryCastAs: (node, typir) => {
        const tryType = typir.Inference.inferType(node.expr);
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
            areTypesEqual,
            isKnownAssignable
          ) ?? InferenceRuleNotApplicable
        );
      },
      ConstMemory: (node, typir) => {
        const expectedReferenceType = getExpectedReferenceType(
          node,
          typeContext
        );
        if (expectedReferenceType) {
          return expectedReferenceType;
        }

        let ancestor = node.$container as AstNode | undefined;
        while (ancestor) {
          if (ancestor.$type === "Deref") {
            const expectedDerefType = findExpectedType(ancestor, typeContext);
            if (!Array.isArray(expectedDerefType) && expectedDerefType) {
              return getOrCreateReferenceType(expectedDerefType, node);
            }
          }
          ancestor = ancestor.$container as AstNode | undefined;
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
          const expected = getExpectedListType(node, typeContext);
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

        const expectedListType = getExpectedListType(node, typeContext);
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
        const expectedSum = getExpectedSumType(node, typeContext);
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
        const expectedSum = getExpectedSumType(node, typeContext);
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
              areTypesEqual,
              isKnownAssignable
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
              areTypesEqual,
              isKnownAssignable
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

        const container = node.$container as AstNode | undefined;
        if (
          container?.$type === "Deref" &&
          (container as { expr?: AstNode }).expr === node
        ) {
          const expectedDerefType = findExpectedType(container, typeContext);
          if (!Array.isArray(expectedDerefType) && expectedDerefType) {
            return getOrCreateReferenceType(expectedDerefType, node);
          }
        }

        const t1 = typir.Inference.inferType(node.thenExpr);
        if (Array.isArray(t1)) return InferenceRuleNotApplicable;

        const t2 = typir.Inference.inferType(node.elseExpr);
        if (Array.isArray(t2)) return InferenceRuleNotApplicable;

        if (t1 && t2) {
          return (
            getCompatibleExpressionType(
              t1,
              t2,
              typeBottom,
              areTypesEqual,
              isKnownAssignable
            ) ?? InferenceRuleNotApplicable
          );
        }

        const expected = findExpectedType(node, typeContext);
        return expected ?? InferenceRuleNotApplicable;
      },
      PatternVar: (node, typir) => {
        const expectedType = getExpectedPatternType(node, typir, {
          typeNat,
          typeBool,
          typeUnit,
          typeAuto,
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
      LetRec: (node, typir) => {
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
      TypeCast: (node, typir) => {
        const castType = typir.Inference.inferType(node.type);
        return Array.isArray(castType) ? InferenceRuleNotApplicable : castType;
      },
      ParenthesisedExpr: (node, typir) => {
        const innerType = typir.Inference.inferType(node.expr);
        return Array.isArray(innerType) ? InferenceRuleNotApplicable : innerType;
      },
      
    });

    typir.validation.Collector.addValidationRulesForAstNodes({
      DeclFun: (node, accept, typir) => {
        if (!node.returnType) {
          return;
        }

        if (
          typir.Inference.inferType(node.returnType) === typeAuto &&
          isVar(node.returnExpr) &&
          node.returnExpr.ref.ref === node
        ) {
          accept({
            severity: "error",
            code: "ERROR_OCCURS_CHECK_INFINITE_TYPE",
            message: "Type reconstruction would require an infinite type.",
            languageNode: node.returnExpr,
          });
        }

        const declaredReturnType = typir.Inference.inferType(node.returnType);

        if (declaredReturnType !== typeAuto) {
          const returnedFunctionType = getDirectFunctionValueType(node.returnExpr);
          if (
            returnedFunctionType &&
            !Array.isArray(declaredReturnType) &&
            !isKnownAssignable(returnedFunctionType, declaredReturnType)
          ) {
            accept({
              severity: "error",
              code: "ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION",
              message: `The return type of function ${node.name} is ${userRepr(returnedFunctionType)}, but the declared return type is ${userRepr(declaredReturnType)}`,
              languageNode: node.returnExpr,
            });
            return;
          }

          if (
            !Array.isArray(declaredReturnType) &&
            node.returnExpr.$type === "Record" &&
            recordTypeLookup.has(declaredReturnType)
          ) {
            return;
          }

          const actualReturnType = typir.Inference.inferType(node.returnExpr);
          if (
            !Array.isArray(declaredReturnType) &&
            declaredReturnType &&
            !Array.isArray(actualReturnType) &&
            actualReturnType &&
            isKnownAssignable(actualReturnType, declaredReturnType)
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
      DeclFunGeneric: (node, accept, typir) => {
        const seen = new Set<string>();
        for (const generic of node.generics) {
          if (seen.has(generic.name)) {
            accept({
              severity: "error",
              code: "ERROR_DUPLICATE_TYPE_PARAMETER",
              message: `Duplicate type parameter '${generic.name}'.`,
              languageNode: generic,
            });
          }
          seen.add(generic.name);
        }

        if (!node.returnType) {
          return;
        }

        const declaredReturnType = typir.Inference.inferType(node.returnType);
        if (
          !Array.isArray(declaredReturnType) &&
          declaredReturnType &&
          declaredReturnType !== typeAuto
        ) {
          const actualReturnType = typir.Inference.inferType(node.returnExpr);
          if (
            !Array.isArray(actualReturnType) &&
            actualReturnType &&
            !isKnownAssignable(actualReturnType, declaredReturnType)
          ) {
            accept({
              severity: "error",
              code: "ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION",
              message: `The return type of generic function ${node.name} is ${userRepr(actualReturnType)}, but the declared return type is ${userRepr(declaredReturnType)}`,
              languageNode: node.returnExpr,
            });
          }
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
            code: "ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION",
            message: `The condition of 'if' must have type ${userRepr(expected)}, but it has type ${userRepr(actual)}`,
          })
        );
        }

        const thenType = typir.Inference.inferType(node.thenExpr);
        const elseType = typir.Inference.inferType(node.elseExpr);
        const expectedType = findExpectedType(node, typeContext);
        const thenCallableType =
          getDirectFunctionValueType(node.thenExpr) ??
          getCallableType(node.thenExpr, typir);
        const elseCallableType =
          getDirectFunctionValueType(node.elseExpr) ??
          getCallableType(node.elseExpr, typir);
        if (
          thenCallableType &&
          elseCallableType &&
          isFunctionType(thenCallableType) &&
          isFunctionType(elseCallableType) &&
          !areTypesEqual(thenCallableType, elseCallableType)
        ) {
          accept({
            severity: "error",
            code: "ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION",
            message: `The 'else' branch of 'if' must have type ${userRepr(thenCallableType)}, but it has type ${userRepr(elseCallableType)}`,
            languageNode: node.elseExpr,
          });
          return;
        }

        if (
          !Array.isArray(thenType) &&
          thenType &&
          !Array.isArray(elseType) &&
          elseType
        ) {
          if (
            getCompatibleExpressionType(
              thenType,
              elseType,
              typeBottom,
              areTypesEqual,
              isKnownAssignable
            )
          ) {
            return;
          }

          if (
            expectedType &&
            isKnownAssignable(thenType, expectedType) &&
            isKnownAssignable(elseType, expectedType)
          ) {
            return;
          }
        }

        if (
          isVar(node.thenExpr) &&
          isVar(node.elseExpr) &&
          node.thenExpr.ref.ref?.$type === "DeclFun" &&
          node.elseExpr.ref.ref?.$type === "DeclFun" &&
          thenCallableType &&
          elseCallableType &&
          !areTypesEqual(thenCallableType, elseCallableType)
        ) {
          accept({
            severity: "error",
            code: "ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION",
            message: `The branches of 'if' have incompatible function types.`,
            languageNode: node,
          });
          return;
        }

        if (
          thenCallableType &&
          elseCallableType &&
          isFunctionType(thenCallableType) &&
          isFunctionType(elseCallableType) &&
          !areTypesEqual(thenCallableType, elseCallableType)
        ) {
          if (
            !isKnownAssignable(elseCallableType, thenCallableType)
          ) {
            accept({
              severity: "error",
              code: "ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION",
              message: `The 'else' branch of 'if' must have type ${userRepr(thenCallableType)}, but it has type ${userRepr(elseCallableType)}`,
              languageNode: node.elseExpr,
            });
            return;
          }
        }

        if (!Array.isArray(thenType) && thenType) {
          return typir.validation.Constraints.ensureNodeIsAssignable(
            node.elseExpr,
            thenType,
            accept,
            (actual, expected) => ({
              message: `The 'else' branch of 'if' must have type ${userRepr(expected)}, but it has type ${userRepr(actual)}`,
            })
          );
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
        const fromCastPattern =
          isVar(node.n) &&
          node.n.ref.ref?.$type === "PatternVar" &&
          (hasAncestor(node.n.ref.ref as AstNode, "PatternCastAs") ||
            hasAncestor(node.n.ref.ref as AstNode, "TryCastAs"));
        return typir.validation.Constraints.ensureNodeIsAssignable(
          node.n,
          typeNat,
          accept,
          (actual, expected) => ({
            code: fromCastPattern
              ? "ERROR_UNEXPECTED_SUBTYPE"
              : "ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION",
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
        const selfAppliedRef = isVar(node.fun) ? node.fun.ref.ref : undefined;
        if (
          selfAppliedRef &&
          node.args.some((arg) => isVar(arg) && arg.ref.ref === selfAppliedRef)
        ) {
          accept({
            severity: "error",
            code: "ERROR_OCCURS_CHECK_INFINITE_TYPE",
            message: "Type reconstruction would require an infinite type.",
            languageNode: node,
          });
          return;
        }

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
                typeContext
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
          const underlyingFunctionExpr = unwrapParenthesisedExpr(node.fun);
          const panicLikeFunction =
            containsNodeType(underlyingFunctionExpr, "Panic") ||
            containsNodeType(underlyingFunctionExpr, "Throw");
          accept({
            severity: "error",
            code:
              panicLikeFunction
                ? containsNodeType(underlyingFunctionExpr, "Panic")
                  ? "ERROR_AMBIGUOUS_PANIC_TYPE"
                  : "ERROR_AMBIGUOUS_THROW_TYPE"
                : underlyingFunctionExpr.$type === "NatRec"
                  ? "ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION"
                  : "ERROR_NOT_A_FUNCTION",
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
          const expectedType = typir.infrastructure.TypeResolver.resolve(
            inputs[index].type
          );
          const actualType = typir.Inference.inferType(node.args[index]);
          if (
            !Array.isArray(actualType) &&
            actualType &&
            isKnownAssignable(actualType, expectedType)
          ) {
            continue;
          }

          typir.validation.Constraints.ensureNodeIsAssignable(
            node.args[index],
            expectedType,
            accept,
            (actual, expected) => ({
              message: `Argument ${index + 1} must have type ${userRepr(expected)}, but it has type ${userRepr(actual)}.`,
            })
          );
        }
      },
      TypeApplication: (node, accept, typir) => {
        if (isVar(node.fun) && node.fun.ref.ref?.$type === "DeclFun") {
          const functionType = typir.Inference.inferType(node.fun.ref.ref);
          accept({
            severity: "error",
            code: "ERROR_NOT_A_GENERIC_FUNCTION",
            message: `Only generic functions can receive type arguments, but this expression has type ${
              !Array.isArray(functionType) && functionType
                ? userRepr(functionType)
                : "unknown"
            }.`,
            languageNode: node.fun,
          });
          return;
        }

        const genericType = typir.Inference.inferType(node.fun);
        if (Array.isArray(genericType) || !genericType) {
          return;
        }

        const forall = forallTypeLookup.get(genericType);
        if (!forall) {
          accept({
            severity: "error",
            code: "ERROR_NOT_A_GENERIC_FUNCTION",
            message: `Only generic functions can receive type arguments, but this expression has type ${userRepr(genericType)}.`,
            languageNode: node.fun,
          });
          return;
        }

        if (forall.params.length !== node.types.length) {
          accept({
            severity: "error",
            code: "ERROR_INCORRECT_NUMBER_OF_TYPE_ARGUMENTS",
            message: `This generic function expects ${forall.params.length} type argument(s), but ${node.types.length} were provided.`,
            languageNode: node,
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

        if (
          !hasExtension(node, Extensions.AmbiguousTypeAsBottom) &&
          !findNonInferenceDrivenExpectedType(node, typeContext)
        ) {
          accept({
            severity: "error",
            code: "ERROR_AMBIGUOUS_THROW_TYPE",
            message:
              "cannot infer type for throw (use type ascriptions or enable #ambiguous-type-as-bottom)",
            languageNode: node,
          });
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
            areTypesEqual,
            isKnownAssignable
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
            areTypesEqual,
            isKnownAssignable
          )
        ) {
          accept({
            severity: "error",
            message: `The try-expression has type ${userRepr(tryType)}, but the catch fallback has type ${userRepr(fallbackType)}.`,
            languageNode: node.fallbackExpr,
          });
        }
      },
      TryCastAs: (node, accept, typir) => {
        const scrutineeType = typir.Inference.inferType(node.tryExpr);
        const castType = typir.Inference.inferType(node.type);
        if (
          Array.isArray(scrutineeType) ||
          Array.isArray(castType) ||
          !scrutineeType ||
          !castType
        ) {
          return;
        }

        if (
          !isKnownAssignable(castType, scrutineeType) &&
          !isKnownAssignable(scrutineeType, castType)
        ) {
          accept({
            severity: "error",
            code: "ERROR_UNEXPECTED_SUBTYPE",
            message: `Cannot cast ${userRepr(scrutineeType)} as unrelated type ${userRepr(castType)}.`,
            languageNode: node,
          });
        }

        validatePatternAgainstType(node.pattern, castType, accept, {
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
      },
      LetRec: (node, accept, typir) => {
        for (const binding of node.patternBindings) {
          if (binding.pattern.$type !== "PatternVar") {
            continue;
          }

          const rhsNode = binding.rhs as AstNode;
          if (rhsNode.$type !== "Abstraction") {
            continue;
          }

          const rhsReturnExpr = (rhsNode as { returnExpr?: AstNode }).returnExpr;
          if (rhsReturnExpr?.$type === "Abstraction") {
            accept({
              severity: "error",
              code: "ERROR_AMBIGUOUS_PATTERN_TYPE",
              message: "cannot infer the type for recursive pattern binding",
              languageNode: binding.pattern,
            });
          }
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
            code: "ERROR_AMBIGUOUS_REFERENCE_TYPE",
            message:
              "Cannot infer the referenced type of a memory address literal. Add an annotation like '<0x0> as &T' or use it where a reference type is expected.",
            languageNode: node,
          });
        }
      },
      Panic: (node, accept, typir) => {
        if (
          hasExtension(node, Extensions.AmbiguousTypeAsBottom) ||
          findNonInferenceDrivenExpectedType(node, typeContext) ||
          (findExpectedType(node, typeContext) &&
            !hasApplicationFunctionAncestor(node)) ||
          hasTypeConstrainingContext(node)
        ) {
          return;
        }

        accept({
          severity: "error",
          code: "ERROR_AMBIGUOUS_PANIC_TYPE",
          message:
            "cannot infer type for panic (use type ascriptions or enable #ambiguous-type-as-bottom)",
          languageNode: node,
        });
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
      TypeAbstraction: (node, accept) => {
        const seen = new Set<string>();
        for (const generic of node.generics) {
          if (seen.has(generic.name)) {
            accept({
              severity: "error",
              code: "ERROR_DUPLICATE_TYPE_PARAMETER",
              message: `Duplicate type parameter '${generic.name}'.`,
              languageNode: generic,
            });
          }
          seen.add(generic.name);
        }
      },
      TypeForAll: (node, accept) => {
        const seen = new Set<string>();
        for (const generic of node.types) {
          if (seen.has(generic.name)) {
            accept({
              severity: "error",
              code: "ERROR_DUPLICATE_TYPE_PARAMETER",
              message: `Duplicate type parameter '${generic.name}'.`,
              languageNode: generic,
            });
          }
          seen.add(generic.name);
        }
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
        const directExpected = findDirectExpectedType(node, typeContext);
        const ascribedType = typir.Inference.inferType(node.type);
        const actualType = typir.Inference.inferType(node.expr);
        if (
          directExpected &&
          !Array.isArray(directExpected) &&
          ascribedType &&
          !Array.isArray(ascribedType) &&
          !isKnownAssignable(ascribedType, directExpected)
        ) {
          accept({
            severity: "error",
            code: "ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION",
            message: `An expression annotated with 'as' has type ${userRepr(ascribedType)}, but ${userRepr(directExpected)} is expected.`,
            languageNode: node.expr,
          });
        }

        if (
          !hasExtension(node, Extensions.StructuralSubtyping) &&
          ascribedType &&
          !Array.isArray(ascribedType) &&
          actualType &&
          !Array.isArray(actualType)
        ) {
          const actualRecord = recordTypeLookup.get(actualType);
          const ascribedRecord = recordTypeLookup.get(ascribedType);
          if (
            actualRecord &&
            ascribedRecord &&
            !areRecordsExactlyCompatible(actualRecord, ascribedRecord, areTypesEqual)
          ) {
            accept({
              severity: "error",
              code: "ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION",
              message: `An expression annotated with 'as' must have type ${userRepr(ascribedType)}, but it has type ${userRepr(actualType)}`,
              languageNode: node.expr,
            });
            return;
          }
        }

        return typir.validation.Constraints.ensureNodeIsAssignable(
          node.expr,
          node.type,
          accept,
          (actual, expected) => ({
            code:
              node.expr.$type === "Inl" || node.expr.$type === "Inr"
                ? "ERROR_UNEXPECTED_INJECTION"
                : "ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION",
            message: `An expression annotated with 'as' must have type ${userRepr(expected)}, but it has type ${userRepr(actual)}`,
          })
        );
      },
      TypeCast: (node, accept, typir) => {
        const actualType = typir.Inference.inferType(node.expr);
        const castType = typir.Inference.inferType(node.type);
        if (
          Array.isArray(actualType) ||
          Array.isArray(castType) ||
          !actualType ||
          !castType
        ) {
          return;
        }

        if (
          !isKnownAssignable(actualType, castType) &&
          !isKnownAssignable(castType, actualType)
        ) {
          accept({
            severity: "error",
            code: "ERROR_UNEXPECTED_SUBTYPE",
            message: `Cannot cast ${userRepr(actualType)} as unrelated type ${userRepr(castType)}.`,
            languageNode: node.expr,
          });
        }

        const directExpected = findDirectExpectedType(node, typeContext);
        if (
          directExpected &&
          !Array.isArray(directExpected) &&
          !isKnownAssignable(castType, directExpected)
        ) {
          accept({
            severity: "error",
            code: "ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION",
            message: `Cast result has type ${userRepr(castType)}, but ${userRepr(directExpected)} is expected.`,
            languageNode: node,
          });
        }
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

        const expectedRecordType = getExpectedRecordType(node, typeContext);
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
        const unexpectedFields = [...actualBindings.keys()].filter(
          (label) => !expectedFields.has(label)
        );
        const allowRecordWidth = hasExtension(
          node,
          Extensions.StructuralSubtyping
        );
        if (missingFields.length > 0) {
          accept({
            severity: "error",
            code: "ERROR_MISSING_RECORD_FIELDS",
            message: `Missing record field(s): ${missingFields.join(", ")}.`,
            languageNode: node,
          });
        }
        if (!allowRecordWidth && unexpectedFields.length > 0) {
          accept({
            severity: "error",
            code: "ERROR_UNEXPECTED_RECORD_FIELDS",
            message: `Unexpected record field(s): ${unexpectedFields.join(", ")}.`,
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

          if (
            isTypeCompatibleWithAuto(
              actualFieldType,
              expectedFieldType,
              typeContext
            ) ||
            isKnownAssignable(actualFieldType, expectedFieldType)
          ) {
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
        const openExceptionPayloadType = getDeclaredExceptionVariantPayloadType(
          node,
          node.label,
          typir
        );
        if (
          openExceptionPayloadType &&
          node.$container?.$type === "Throw" &&
          (node.$container as { expr?: AstNode }).expr === node
        ) {
          if (!node.rhs) {
            accept({
              severity: "error",
              message: `Exception variant '${node.label}' requires a value of type ${userRepr(openExceptionPayloadType)}.`,
              languageNode: node,
              languageProperty: "label",
            });
            return;
          }

          typir.validation.Constraints.ensureNodeIsAssignable(
            node.rhs,
            openExceptionPayloadType,
            accept,
            (actual, expectedTypeAnnotation) => ({
              message: `Exception variant '${node.label}' expects ${userRepr(expectedTypeAnnotation)}, but got ${userRepr(actual)}.`,
            })
          );
          return;
        }

        const expected = getExpectedVariantType(node, typeContext);
        if (!expected || Array.isArray(expected)) {
          accept({
            severity: "error",
            code: "ERROR_AMBIGUOUS_VARIANT_TYPE",
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
        if (containsNodeType(node.expr, "Panic")) {
          accept({
            severity: "error",
            code: "ERROR_AMBIGUOUS_PANIC_TYPE",
            message: "cannot infer type for panic before tuple projection",
            languageNode: node.expr,
          });
          return;
        }

        if (isVar(node.expr) && node.expr.ref.ref?.$type === "DeclFun") {
          accept({
            severity: "error",
            code: "ERROR_NOT_A_TUPLE",
            message: "Pair projection expects a pair, but the expression is a function.",
            languageNode: node,
            languageProperty: "expr",
          });
          return;
        }

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
            code: "ERROR_NOT_A_TUPLE",
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
            code: "ERROR_NOT_A_RECORD",
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
          const expected = getExpectedListType(node, typeContext);
          if (!expected) {
            accept({
              severity: "error",
              code: "ERROR_AMBIGUOUS_LIST_TYPE",
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

        const expectedListType = getExpectedListType(node, typeContext);
        const expectedElementType = expectedListType
          ? listTypeLookup.get(expectedListType)
          : undefined;
        if (expectedElementType) {
          for (const expr of node.exprs) {
            typir.validation.Constraints.ensureNodeIsAssignable(
              expr,
              expectedElementType,
              accept,
              (actual, expected) => ({
                code: "ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION",
                message: `List element must have type ${userRepr(expected)}, but has ${userRepr(actual)}.`,
              })
            );
          }
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

        const headType = typir.Inference.inferType(node.head);
        const headReferenceType =
          !Array.isArray(headType) && headType
            ? referenceTypeLookup.get(headType)
            : undefined;
        if (headReferenceType && areTypesEqual(headReferenceType, elementType)) {
          return;
        }

        typir.validation.Constraints.ensureNodeIsAssignable(
          node.head,
          elementType,
          accept,
          (actual, expected) => ({
            code: "ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION",
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
        const directExpected = findDirectExpectedType(node, typeContext);
        if (
          directExpected &&
          !Array.isArray(directExpected) &&
          !sumTypeLookup.has(directExpected)
        ) {
          accept({
            severity: "error",
            code: "ERROR_UNEXPECTED_INJECTION",
            message: `This expression is expected to have type ${userRepr(directExpected)}, but it is an 'inl' sum injection.`,
            languageNode: node,
          });
        }

        const expectedSum = getExpectedSumType(node, typeContext);
        if (
          expectedSum &&
          hasApplicationFunctionAncestor(node) &&
          !hasExtension(node, Extensions.TypeReconstruction) &&
          !hasExtension(node, Extensions.AmbiguousTypeAsBottom) &&
          !findNonInferenceDrivenExpectedType(node, typeContext)
        ) {
          accept({
            severity: "error",
            code: "ERROR_AMBIGUOUS_SUM_TYPE",
            message:
              "It is not possible to output the amount type for 'inl'. Add an annotation of the form 'as <T + U>' or use it in the context of the expected type.",
            languageNode: node,
          });
          return;
        }

        if (!expectedSum || Array.isArray(expectedSum)) {
          accept({
            severity: "error",
            code: "ERROR_AMBIGUOUS_SUM_TYPE",
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
        const directExpected = findDirectExpectedType(node, typeContext);
        if (
          directExpected &&
          !Array.isArray(directExpected) &&
          !sumTypeLookup.has(directExpected)
        ) {
          accept({
            severity: "error",
            code: "ERROR_UNEXPECTED_INJECTION",
            message: `This expression is expected to have type ${userRepr(directExpected)}, but it is an 'inr' sum injection.`,
            languageNode: node,
          });
        }

        const expectedSum = getExpectedSumType(node, typeContext);
        if (
          expectedSum &&
          hasApplicationFunctionAncestor(node) &&
          !hasExtension(node, Extensions.TypeReconstruction) &&
          !hasExtension(node, Extensions.AmbiguousTypeAsBottom) &&
          !findNonInferenceDrivenExpectedType(node, typeContext)
        ) {
          accept({
            severity: "error",
            code: "ERROR_AMBIGUOUS_SUM_TYPE",
            message:
              "It is not possible to output the amount type for 'inr'. Add an annotation of the form 'as <T + U>' or use it in the context of the expected type.",
            languageNode: node,
          });
          return;
        }

        if (!expectedSum || Array.isArray(expectedSum)) {
          accept({
            severity: "error",
            code: "ERROR_AMBIGUOUS_SUM_TYPE",
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
          const expectedType = findExpectedType(node, typeContext);
          for (const branchType of branchTypes.slice(1)) {
            if (
              !getCompatibleExpressionType(
                reference,
                branchType,
                typeBottom,
                areTypesEqual,
                isKnownAssignable
              )
            ) {
              if (
                expectedType &&
                branchTypes.every((type) =>
                  isKnownAssignable(type, expectedType)
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
          matching: (otherNode) => otherNode === node, 
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

function isStructurallyAssignable(
  source: TypirType,
  target: TypirType,
  context: StellaTypeContext,
  seen = new Set<string>()
): boolean {
  if (context.areTypesEqual(source, target)) {
    return true;
  }
  if (source === context.typeBottom || target === context.typeTop) {
    return true;
  }

  if (context.typeVariableLookup.has(source) || context.typeVariableLookup.has(target)) {
    return source === target;
  }

  const key = `${source.getIdentifier()}<=${target.getIdentifier()}`;
  if (seen.has(key)) {
    return true;
  }
  seen.add(key);

  const sourceForall = context.forallTypeLookup.get(source);
  const targetForall = context.forallTypeLookup.get(target);
  if (sourceForall || targetForall) {
    if (
      !sourceForall ||
      !targetForall ||
      sourceForall.params.length !== targetForall.params.length
    ) {
      return false;
    }

    const substitutions = new Map<TypirType, TypirType>();
    for (let index = 0; index < sourceForall.params.length; index++) {
      substitutions.set(targetForall.params[index], sourceForall.params[index]);
    }
    return isStructurallyAssignable(
      sourceForall.body,
      context.substituteType(targetForall.body, substitutions),
      context,
      seen
    );
  }

  const sourceTuple = context.tupleTypeLookup.get(source);
  const targetTuple = context.tupleTypeLookup.get(target);
  if (sourceTuple && targetTuple) {
    return (
      sourceTuple.length === targetTuple.length &&
      sourceTuple.every((component, index) =>
        isStructurallyAssignable(component, targetTuple[index], context, seen)
      )
    );
  }

  const sourceSum = context.sumTypeLookup.get(source);
  const targetSum = context.sumTypeLookup.get(target);
  if (sourceSum && targetSum) {
    return (
      isStructurallyAssignable(sourceSum[0], targetSum[0], context, seen) &&
      isStructurallyAssignable(sourceSum[1], targetSum[1], context, seen)
    );
  }

  const sourceRecord = context.recordTypeLookup.get(source);
  const targetRecord = context.recordTypeLookup.get(target);
  if (sourceRecord && targetRecord) {
    return [...targetRecord.entries()].every(([label, targetField]) => {
      const sourceField = sourceRecord.get(label);
      return (
        sourceField !== undefined &&
        isStructurallyAssignable(sourceField, targetField, context, seen)
      );
    });
  }

  const sourceVariant = context.variantTypeLookup.get(source);
  const targetVariant = context.variantTypeLookup.get(target);
  if (sourceVariant && targetVariant) {
    return [...sourceVariant.entries()].every(([label, sourcePayload]) => {
      if (!targetVariant.has(label)) {
        return false;
      }
      const targetPayload = targetVariant.get(label);
      if (sourcePayload === undefined || targetPayload === undefined) {
        return sourcePayload === targetPayload;
      }
      return isStructurallyAssignable(
        sourcePayload,
        targetPayload,
        context,
        seen
      );
    });
  }

  const sourceList = context.listTypeLookup.get(source);
  const targetList = context.listTypeLookup.get(target);
  if (sourceList && targetList) {
    return isStructurallyAssignable(sourceList, targetList, context, seen);
  }

  const sourceReference = context.referenceTypeLookup.get(source);
  const targetReference = context.referenceTypeLookup.get(target);
  if (sourceReference && targetReference) {
    return (
      isStructurallyAssignable(sourceReference, targetReference, context, seen) &&
      isStructurallyAssignable(targetReference, sourceReference, context, seen)
    );
  }

  if (isFunctionType(source) && isFunctionType(target)) {
    const sourceInputs = source.getInputs();
    const targetInputs = target.getInputs();
    const sourceOutput = source.getOutput("RETURN_UNDEFINED")?.type;
    const targetOutput = target.getOutput("RETURN_UNDEFINED")?.type;
    if (
      sourceInputs.length !== targetInputs.length ||
      !sourceOutput ||
      !targetOutput
    ) {
      return false;
    }

    return (
      isStructurallyAssignable(
        context.typir.infrastructure.TypeResolver.resolve(sourceOutput),
        context.typir.infrastructure.TypeResolver.resolve(targetOutput),
        context,
        seen
      ) &&
      sourceInputs.every((sourceInput, index) =>
        isStructurallyAssignable(
          context.typir.infrastructure.TypeResolver.resolve(
            targetInputs[index].type
          ),
          context.typir.infrastructure.TypeResolver.resolve(sourceInput.type),
          context,
          seen
        )
      )
    );
  }

  return false;
}

function areRecordsExactlyCompatible(
  actual: Map<string, TypirType>,
  expected: Map<string, TypirType>,
  areTypesEqual: (left: TypirType, right: TypirType) => boolean
): boolean {
  if (actual.size !== expected.size) {
    return false;
  }

  for (const [label, expectedType] of expected) {
    const actualType = actual.get(label);
    if (!actualType || !areTypesEqual(actualType, expectedType)) {
      return false;
    }
  }

  return true;
}

function findExpectedType(
  node: AstNode,
  context: StellaTypeContext
): TypirType | undefined {
  return resolveExpectedType(node, context, "full");
}

function findNonInferenceDrivenExpectedType(
  node: AstNode,
  context: StellaTypeContext
): TypirType | undefined {
  return resolveExpectedType(node, context, "nonInferenceDriven");
}

function findContainerExpectedType(
  node: AstNode,
  context: StellaTypeContext
): TypirType | undefined {
  return resolveExpectedType(node, context, "container");
}

function findDirectExpectedType(
  node: AstNode,
  context: StellaTypeContext
): TypirType | undefined {
  return resolveExpectedType(node, context, "direct");
}

function resolveExpectedType(
  node: AstNode,
  context: StellaTypeContext,
  mode: ExpectedTypeMode
): TypirType | undefined {
  switch (mode) {
    case "full":
      return resolveFullExpectedType(node, context);
    case "nonInferenceDriven":
      return resolveNonInferenceDrivenExpectedType(node, context);
    case "container":
      return resolveContainerExpectedType(node, context);
    case "direct":
      return resolveDirectExpectedType(node, context);
  }
}

function resolveFullExpectedType(
  node: AstNode,
  context: StellaTypeContext
): TypirType | undefined {
  const typir = context.typir;
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
      const expectedAbstraction = findExpectedType(container, context);
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

    if ((container as { $type?: string; rhs?: unknown }).$type === "Binding") {
      const binding = container as unknown as {
        name: string;
        rhs: AstNode;
        $container?: AstNode;
      };
      if (binding.rhs === current && binding.$container?.$type === "Record") {
        const expectedRecord = findExpectedType(binding.$container, context);
        if (expectedRecord && !Array.isArray(expectedRecord)) {
          const expectedFields = context.recordTypeLookup.get(expectedRecord);
          const expectedField = expectedFields?.get(binding.name);
          if (expectedField) {
            return expectedField;
          }
        }
      }
    }

    if (container.$type === "Tuple") {
      const tuple = container as unknown as { exprs: AstNode[] };
      const index = tuple.exprs.indexOf(current as never);
      if (index >= 0) {
        const expectedTuple = findExpectedType(container, context);
        const expectedComponents = expectedTuple
          ? context.tupleTypeLookup.get(expectedTuple)
          : undefined;
        if (expectedComponents && index < expectedComponents.length) {
          return expectedComponents[index];
        }
      }
    }

    if (container.$type === "List") {
      const list = container as unknown as { exprs: AstNode[] };
      if (list.exprs.includes(current as never)) {
        const expectedList = findExpectedType(container, context);
        const elementType = expectedList
          ? context.listTypeLookup.get(expectedList)
          : undefined;
        if (elementType) {
          return elementType;
        }
      }
    }

    if (container.$type === "ConsList") {
      const cons = container as unknown as { head: AstNode; tail: AstNode };
      if (cons.head === current) {
        const tailType = typir.Inference.inferType(cons.tail);
        const tailElementType =
          !Array.isArray(tailType) && tailType
            ? context.listTypeLookup.get(tailType)
            : undefined;
        if (tailElementType) {
          return tailElementType;
        }

        const expectedList = findExpectedType(container, context);
        const expectedElement = expectedList
          ? context.listTypeLookup.get(expectedList)
          : undefined;
        if (expectedElement) {
          return expectedElement;
        }
      } else if (cons.tail === current) {
        const expectedList = findExpectedType(container, context);
        if (expectedList) {
          return expectedList;
        }
      }
    }

    if ((container as { $type?: string; rhs?: unknown }).$type === "Variant") {
      const variant = container as unknown as {
        label: string;
        rhs?: AstNode;
      };
      if (variant.rhs === current) {
        const expectedVariant = findExpectedType(container, context);
        const expectedFields = expectedVariant
          ? context.variantTypeLookup.get(expectedVariant)
          : undefined;
        const expectedPayload = expectedFields?.get(variant.label);
        if (expectedPayload) {
          return expectedPayload;
        }
      }
    }

    if (container.$type === Application.$type) {
      const application = container as Application;
      if (application.fun === current) {
        return undefined;
      }
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

    if (
      container.$type === "DotRecord" &&
      (container as { expr?: AstNode }).expr === current
    ) {
      return undefined;
    }

    if (
      container.$type === "DotTuple" &&
      (container as { expr?: AstNode }).expr === current
    ) {
      return undefined;
    }

    if ((container as MatchCase).expr === current) {
      const matchNode = (container as MatchCase).$container as Match | undefined;
      if (matchNode) {
        const expected = findContainerExpectedType(matchNode, context);
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
        const expected = findContainerExpectedType(container, context);
        if (expected) {
          return expected;
        }

        const sibling =
          ifNode.thenExpr === current ? ifNode.elseExpr : ifNode.thenExpr;
        const siblingType = typir.Inference.inferType(sibling);
        if (!Array.isArray(siblingType) && siblingType) {
          return siblingType;
        }
      }
    }

    current = container;
    container = container.$container as AstNode | undefined;
  }

  return undefined;
}

function resolveNonInferenceDrivenExpectedType(
  node: AstNode,
  context: StellaTypeContext
): TypirType | undefined {
  const typir = context.typir;
  let current: AstNode | undefined = node;
  let container = node.$container as AstNode | undefined;

  while (container) {
    if ((container as { $type?: string; expr?: unknown }).$type === "TypeAsc") {
      const typeAsc = container as { type?: AstNode; expr?: AstNode };
      if (typeAsc.expr === current && typeAsc.type) {
        const expected = typir.Inference.inferType(typeAsc.type);
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

    if ((container as { $type?: string; rhs?: unknown }).$type === "Binding") {
      const binding = container as unknown as {
        name: string;
        rhs: AstNode;
        $container?: AstNode;
      };
      if (binding.rhs === current && binding.$container?.$type === "Record") {
        const expectedRecord = findNonInferenceDrivenExpectedType(
          binding.$container,
          context
        );
        if (expectedRecord) {
          const expectedFields = context.recordTypeLookup.get(expectedRecord);
          const expectedField = expectedFields?.get(binding.name);
          if (expectedField) {
            return expectedField;
          }
        }
      }
    }

    if (container.$type === Application.$type) {
      const application = container as Application;
      if (application.fun === current) {
        return undefined;
      }
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
      }
    }

    if (
      (container as { $type?: string; returnExpr?: unknown }).$type === "Abstraction" &&
      (container as { returnExpr?: unknown }).returnExpr === current
    ) {
      return undefined;
    }

    current = container;
    container = container.$container as AstNode | undefined;
  }

  return undefined;
}

function resolveContainerExpectedType(
  node: AstNode,
  context: StellaTypeContext
): TypirType | undefined {
  const typir = context.typir;
  const container = node.$container as AstNode | undefined;
  if (!container) {
    return undefined;
  }

  if ((container as { $type?: string; expr?: unknown }).$type === "TypeAsc") {
    const typeAsc = container as { type?: AstNode; expr?: AstNode };
    if (typeAsc.expr === node && typeAsc.type) {
      const expected = typir.Inference.inferType(typeAsc.type);
      return !Array.isArray(expected) && expected ? expected : undefined;
    }
  }

  if (
    isDeclFun(container) &&
    container.returnExpr === node &&
    container.returnType
  ) {
    const expected = typir.Inference.inferType(container.returnType);
    return !Array.isArray(expected) && expected ? expected : undefined;
  }

  if ((container as { $type?: string; returnExpr?: unknown }).$type === "Abstraction") {
    const abstraction = container as unknown as { returnExpr?: AstNode };
    if (abstraction.returnExpr === node) {
      const expectedFunction = findContainerExpectedType(container, context);
      if (expectedFunction && isFunctionType(expectedFunction)) {
        const output = expectedFunction.getOutput("RETURN_UNDEFINED")?.type;
        return output ? typir.infrastructure.TypeResolver.resolve(output) : undefined;
      }
    }
  }

  if (container.$type === Application.$type) {
    const application = container as Application;
    const argIndex = application.args.indexOf(node as never);
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

  return undefined;
}

function resolveDirectExpectedType(
  node: AstNode,
  context: StellaTypeContext
): TypirType | undefined {
  const typir = context.typir;
  const container = node.$container as AstNode | undefined;
  if (!container) {
    return undefined;
  }

  if ((container as { $type?: string; expr?: unknown }).$type === "TypeAsc") {
    const typeAsc = container as { type?: AstNode; expr?: AstNode };
    if (typeAsc.expr === node && typeAsc.type) {
      const expected = typir.Inference.inferType(typeAsc.type);
      if (!Array.isArray(expected) && expected) {
        return expected;
      }
    }
  }

  if (
    isDeclFun(container) &&
    container.returnExpr === node &&
    container.returnType
  ) {
    const expected = typir.Inference.inferType(container.returnType);
    if (!Array.isArray(expected) && expected) {
      return expected;
    }
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

function unwrapParenthesisedExpr(node: AstNode): AstNode {
  let current = node;
  while (
    current.$type === "ParenthesisedExpr" &&
    (current as { expr?: AstNode }).expr
  ) {
    current = (current as unknown as { expr: AstNode }).expr;
  }
  return current;
}

function containsNodeType(
  node: AstNode,
  typeName: string,
  seen = new Set<AstNode>()
): boolean {
  if (node.$type === typeName) {
    return true;
  }

  if (seen.has(node)) {
    return false;
  }
  seen.add(node);

  for (const [key, value] of Object.entries(
    node as unknown as Record<string, unknown>
  )) {
    if (key.startsWith("$")) {
      continue;
    }

    if (!value) {
      continue;
    }
    if (Array.isArray(value)) {
      if (
        value.some(
          (item) =>
            typeof item === "object" &&
            item !== null &&
            "$type" in item &&
            containsNodeType(item as AstNode, typeName, seen)
        )
      ) {
        return true;
      }
    } else if (
      typeof value === "object" &&
      "$type" in value &&
      containsNodeType(value as AstNode, typeName, seen)
    ) {
      return true;
    }
  }

  return false;
}

function hasAncestor(node: AstNode, typeName: string): boolean {
  let current = node.$container as AstNode | undefined;
  while (current) {
    if (current.$type === typeName) {
      return true;
    }
    current = current.$container as AstNode | undefined;
  }

  return false;
}

function hasApplicationFunctionAncestor(node: AstNode): boolean {
  let current: AstNode | undefined = node;
  let container = node.$container as AstNode | undefined;

  while (container) {
    if (
      container.$type === Application.$type &&
      (container as Application).fun === current
    ) {
      return true;
    }

    current = container;
    container = container.$container as AstNode | undefined;
  }

  return false;
}

function hasTypeConstrainingContext(node: AstNode): boolean {
  let current: AstNode | undefined = node;
  let container = node.$container as AstNode | undefined;

  while (container) {
    if (
      container.$type === "Application" ||
      container.$type === "DotTuple" ||
      container.$type === "DotRecord"
    ) {
      return true;
    }

    if (
      container.$type === "If" &&
      ((container as { thenExpr?: AstNode }).thenExpr === current ||
        (container as { elseExpr?: AstNode }).elseExpr === current)
    ) {
      current = container;
      container = container.$container as AstNode | undefined;
      continue;
    }

    if (container.$type === "ParenthesisedExpr") {
      current = container;
      container = container.$container as AstNode | undefined;
      continue;
    }

    return false;
  }

  return false;
}

function getDirectReferencedFunction(
  node: AstNode
):
  | (AstNode & {
      $type: "DeclFun";
      paramDecls: Array<{ paramType: AstNode }>;
      returnType?: AstNode;
    })
  | undefined {
  if (!isVar(node)) {
    return undefined;
  }

  const referenced = node.ref.ref as AstNode | undefined;
  if (referenced && referenced.$type === "DeclFun") {
    return referenced as AstNode & {
      $type: "DeclFun";
      paramDecls: Array<{ paramType: AstNode }>;
      returnType?: AstNode;
    };
  }

  return undefined;
}

function getExpectedSumType(
  node: Inl | Inr,
  context: StellaTypeContext
): TypirType | undefined {
  const expected = findExpectedType(node, context);
  if (expected && context.sumTypeLookup.has(expected)) {
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
      context
    );
    if (!outerExpected) {
      return undefined;
    }
    const outerComponents = context.sumTypeLookup.get(outerExpected);
    if (!outerComponents) {
      return undefined;
    }
    return container.$type === "Inl" ? outerComponents[0] : outerComponents[1];
  }

  if (container.$type === "Tuple") {
    const tuple = container as unknown as { exprs: AstNode[] };
    const index = tuple.exprs.indexOf(node as never);
    if (index >= 0) {
      const tupleExpected = findExpectedType(container, context);
      if (tupleExpected) {
        const components = context.tupleTypeLookup.get(tupleExpected);
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
  context: StellaTypeContext
): TypirType | undefined {
  const expected = findExpectedType(node, context);
  return expected && context.listTypeLookup.has(expected) ? expected : undefined;
}

function getExpectedRecordType(
  node: StellaRecord,
  context: StellaTypeContext
): TypirType | undefined {
  const expected = findExpectedType(node, context);
  return expected && context.recordTypeLookup.has(expected)
    ? expected
    : undefined;
}

function getExpectedReferenceType(
  node: ConstMemory,
  context: StellaTypeContext
): TypirType | undefined {
  const typir = context.typir;
  const immediateContainer = node.$container as AstNode | undefined;
  const isImmediateIfBranch =
    immediateContainer?.$type === "If" &&
    ((immediateContainer as { thenExpr?: AstNode }).thenExpr === node ||
      (immediateContainer as { elseExpr?: AstNode }).elseExpr === node);
  const expected = isImmediateIfBranch
    ? undefined
    : findExpectedType(node, context);
  if (expected && context.referenceTypeLookup.has(expected)) {
    return expected;
  }

  let current: AstNode | undefined = node;
  let container = immediateContainer;
  if (!container) return undefined;

  while (container) {
    if ((container as { $type?: string; expr?: unknown }).$type === "TypeAsc") {
      const typeAsc = container as { type?: unknown; expr?: unknown };
      if (typeAsc.expr === current && typeAsc.type) {
        const expected = typir.Inference.inferType(typeAsc.type as AstNode);
        if (!Array.isArray(expected) && context.referenceTypeLookup.has(expected)) {
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
      if (!Array.isArray(expected) && context.referenceTypeLookup.has(expected)) {
        return expected;
      }
    }

    if (container.$type === Application.$type) {
      const application = container as Application;
      const argIndex = application.args.indexOf(current as never);
      if (argIndex >= 0) {
        if (isVar(application.fun)) {
          const declaration = application.fun.ref.ref as DeclFun | undefined;
          const expectedTypeNode = declaration?.paramDecls[argIndex]?.paramType;
          if (expectedTypeNode) {
            const expected = typir.Inference.inferType(expectedTypeNode);
            if (
              !Array.isArray(expected) &&
              context.referenceTypeLookup.has(expected)
            ) {
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
            if (context.referenceTypeLookup.has(expected)) {
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

function getDeclaredExceptionVariantPayloadType(
  node: AstNode,
  label: string,
  typir: TypirServices<StellaSpecifics>
): TypirType | undefined {
  let root: AstNode = node;
  while (root.$container) {
    root = root.$container as AstNode;
  }

  const program = root as { decls?: AstNode[] };
  if (!program.decls) {
    return undefined;
  }

  for (const decl of program.decls) {
    if (
      decl.$type !== "DeclExceptionVariant" ||
      (decl as unknown as { name?: string }).name !== label
    ) {
      continue;
    }

    const variantTypeNode = (decl as unknown as { variantType: AstNode })
      .variantType;
    const variantType = typir.Inference.inferType(variantTypeNode);
    if (!Array.isArray(variantType) && variantType) {
      return variantType;
    }
  }

  return undefined;
}

function getCompatibleExpressionType(
  left: TypirType,
  right: TypirType,
  bottom: TypirType,
  areTypesEqual: (left: TypirType, right: TypirType) => boolean,
  isAssignable?: (left: TypirType, right: TypirType) => boolean
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

  if (isAssignable?.(left, right)) {
    return right;
  }

  if (isAssignable?.(right, left)) {
    return left;
  }

  return undefined;
}

function isTypeCompatibleWithAuto(
  actual: TypirType,
  expected: TypirType,
  context: StellaTypeContext
): boolean {
  const typir = context.typir;
  if (
    actual === context.typeAuto ||
    expected === context.typeAuto ||
    context.areTypesEqual(actual, expected)
  ) {
    return true;
  }

  const actualTuple = context.tupleTypeLookup.get(actual);
  const expectedTuple = context.tupleTypeLookup.get(expected);
  if (actualTuple && expectedTuple) {
    return (
      actualTuple.length === expectedTuple.length &&
      actualTuple.every((type, index) =>
        isTypeCompatibleWithAuto(type, expectedTuple[index], context)
      )
    );
  }

  const actualSum = context.sumTypeLookup.get(actual);
  const expectedSum = context.sumTypeLookup.get(expected);
  if (actualSum && expectedSum) {
    return (
      isTypeCompatibleWithAuto(actualSum[0], expectedSum[0], context) &&
      isTypeCompatibleWithAuto(actualSum[1], expectedSum[1], context)
    );
  }

  const actualRecord = context.recordTypeLookup.get(actual);
  const expectedRecord = context.recordTypeLookup.get(expected);
  if (actualRecord && expectedRecord) {
    if (actualRecord.size !== expectedRecord.size) {
      return false;
    }
    for (const [label, expectedType] of expectedRecord) {
      const actualType = actualRecord.get(label);
      if (
        !actualType ||
        !isTypeCompatibleWithAuto(actualType, expectedType, context)
      ) {
        return false;
      }
    }
    return true;
  }

  const actualVariant = context.variantTypeLookup.get(actual);
  const expectedVariant = context.variantTypeLookup.get(expected);
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
          : !isTypeCompatibleWithAuto(actualType, expectedType, context)
      ) {
        return false;
      }
    }
    return true;
  }

  const actualList = context.listTypeLookup.get(actual);
  const expectedList = context.listTypeLookup.get(expected);
  if (actualList && expectedList) {
    return isTypeCompatibleWithAuto(actualList, expectedList, context);
  }

  const actualRef = context.referenceTypeLookup.get(actual);
  const expectedRef = context.referenceTypeLookup.get(expected);
  if (actualRef && expectedRef) {
    return isTypeCompatibleWithAuto(actualRef, expectedRef, context);
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
      if (!isTypeCompatibleWithAuto(actualInput, expectedInput, context)) {
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
      context
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
    typeAuto: TypirType;
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
    if (binding.$container?.$type === "LetRec") {
      return helpers.typeAuto;
    }

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

  const tryCastAs = AstUtils.getContainerOfType(
    node,
    (candidate): candidate is AstNode & {
      $type: "TryCastAs";
      pattern: AstNode;
      type: AstNode;
    } => candidate.$type === "TryCastAs"
  );
  if (tryCastAs?.pattern) {
    const castType = typir.Inference.inferType(tryCastAs.type);
    if (!Array.isArray(castType) && castType) {
      return resolveNestedPatternType(
        tryCastAs.pattern,
        node,
        castType,
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
    typeAuto: TypirType;
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
  context: StellaTypeContext
): TypirType | undefined {
  const typir = context.typir;
  const expected = findExpectedType(node, context);
  if (expected && context.variantTypeLookup.has(expected)) {
    return expected;
  }

  const container = node.$container as AstNode | undefined;
  if (
    container?.$type === "Throw" &&
    (container as { expr?: AstNode }).expr === node
  ) {
    const exceptionType = getDeclaredExceptionType(container, typir);
    if (exceptionType && context.variantTypeLookup.has(exceptionType)) {
      return exceptionType;
    }
  }

  if (
    container?.$type === "Ref" &&
    (container as { expr?: AstNode }).expr === node
  ) {
    const expectedReference = findExpectedType(container, context);
    if (expectedReference) {
      const referencedType = context.referenceTypeLookup.get(expectedReference);
      if (referencedType && context.variantTypeLookup.has(referencedType)) {
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
