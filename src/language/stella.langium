grammar Stella

entry Program:
    langDecl=LanguageDecl
    extensions+=Extension*
    decls+=Decl*
;

LanguageDecl:
    {infer LanguageDecl}
    'language' 'core' ';'
;

Extension:
    'extend' 'with'
    extensionNames+=EXTENSION_NAME (',' extensionNames+=EXTENSION_NAME)* ';'
;

// Declarations

Decl:
    DeclFun
    | DeclFunGeneric
    | DeclTypeAlias
    | DeclExceptionType
    | DeclExceptionVariant
;

Annotation:
    InlineAnnotation;
InlineAnnotation:
    {infer InlineAnnotation} 'inline';

ParamDecl:
    name=ID ':' paramType=Type;

fragment FuncParamsAndBody:
    '(' (paramDecls+=ParamDecl (',' paramDecls+=ParamDecl)*)? ')'
    ('->' returnType=Type)?
    ('throws' throwTypes+=Type (',' throwTypes+=Type)*)?
    '{' (localDecls+=Decl)* 'return' returnExpr=Expr '}'
;

DeclFun:
    (annotations+=Annotation)* 'fn' name=ID FuncParamsAndBody
;

GenericTypeVar:
    name=ID
;

DeclFunGeneric:
    (annotations+=Annotation)* 'generic' 'fn' name=ID '[' generics+=GenericTypeVar (',' generics+=GenericTypeVar)* ']' FuncParamsAndBody
;

DeclTypeAlias:
    'type' name=ID '=' type=Type;

DeclExceptionType:
    'exception' 'type' '=' exceptionType=Type;

DeclExceptionVariant:
    'exception' 'variant' name=ID ':' variantType=Type;


// Expressions

type DeclValue = ParamDecl | DeclFun | DeclFunGeneric | PatternVar;

ConstTrue:
    {infer ConstTrue} 'true';
ConstFalse:
    {infer ConstFalse} 'false';
ConstUnit:
    {infer ConstUnit} 'unit';
ConstInt:
    {infer ConstInt} n=INT
    | {infer ConstInt} '-' n=INT;
ConstMemory:
    mem=MEMORY_ADDRESS;
Var:
    ref=[DeclValue];
Panic:
    {infer Panic} 'panic!';
Throw:
    'throw' '(' expr=Expr ')';
TryCatch:
    'try' '{' tryExpr=Expr '}' 'catch' '{' pattern=Pattern '=>' fallbackExpr=Expr '}';
TryCastAs:
    'try' '{' tryExpr=Expr '}' 'cast' 'as' type=Type '{' pattern=Pattern '=>' expr=Expr '}' 'with' '{' fallbackExpr=Expr '}';
TryWith:
    'try' '{' tryExpr=Expr '}' 'with' '{' fallbackExpr=Expr '}';
Inl:
    'inl' '(' expr=Expr ')';
Inr:
    'inr' '(' expr=Expr ')';
ConsList:
    ('cons' | 'List::cons') '(' head=Expr ',' tail=Expr ')';
Head:
    'List::head' '(' list=Expr ')';
IsEmpty:
    'List::isempty' '(' list=Expr ')';
Tail:
    'List::tail' '(' list=Expr ')';
Succ:
    'succ' '(' n=Expr ')';
LogicNot:
    'not' '(' expr=Expr ')';
Pred:
    'Nat::pred' '(' n=Expr ')';
IsZero:
    'Nat::iszero' '(' n=Expr ')';
Fix:
    'fix' '(' expr=Expr ')';
NatRec:
    'Nat::rec' '(' n=Expr ',' initial=Expr ',' step=Expr ')';
Fold:
    'fold' '[' type=Type ']' expr=Expr;
Unfold:
    'unfold' '[' type=Type ']' expr=Expr;
Ref:
    'new' '(' expr=Expr ')';
Deref:
    '*' expr=Expr;
Abstraction:
    'fn' '(' (paramDecls+=ParamDecl (',' paramDecls+=ParamDecl)*)? ')'
    '{' 'return' returnExpr=Expr '}'
;
Tuple:
    '{' (exprs+=Expr (',' exprs+=Expr)*)? '}';
Record:
    '{' bindings+=Binding (',' bindings+=Binding)* '}';
Variant:
    '<|' label=ID ('=' rhs=Expr)? '|>';
Match:
    'match' expr=Expr '{' (cases+=MatchCase ('|' cases+=MatchCase)*)? '}';
MatchCase:
    pattern=Pattern '=>' expr=Expr;
List:
    '[' (exprs+=Expr (',' exprs+=Expr)*)? ']'
    | 'List::nil';
If:
    'if' condition=Expr 'then' thenExpr=Expr 'else' elseExpr=Expr;
Let:
    'let' patternBindings+=PatternBinding (',' patternBindings+=PatternBinding)* 'in' body=Expr;
LetRec:
    'letrec' patternBindings+=PatternBinding (',' patternBindings+=PatternBinding)* 'in' body=Expr;
TypeAbstraction:
    'generic' '[' generics+=GenericTypeVar (',' generics+=GenericTypeVar)* ']' expr=Expr;
ParenthesisedExpr:
    '(' expr=Expr ')';

// Left-recursive expressions

Expr:
    Sequence
;

Sequence infers Expr:
    Assign (
          {infer Sequence.expr1=current} ';' expr2=Assign
        | ';'
    )*
;

Assign infers Expr:
    Equal ({infer Assign.left=current} ':=' right=Equal)*
;

Equal infers Expr:
    NotEqual ({infer Equal.left=current} '==' right=NotEqual)*
;
NotEqual infers Expr:
    LessThan ({infer NotEqual.left=current} '!=' right=LessThan)*
;

LessThan infers Expr:
    LessThanOrEqual ({infer LessThan.left=current} '<' right=LessThanOrEqual)*
;

LessThanOrEqual infers Expr:
    GreaterThan ({infer LessThanOrEqual.left=current} '<=' right=GreaterThan)*
;
GreaterThan infers Expr:
    GreaterThanOrEqual ({infer GreaterThan.left=current} '>' right=GreaterThanOrEqual)*
;
GreaterThanOrEqual infers Expr:
    TypeCast ({infer GreaterThanOrEqual.left=current} '>=' right=TypeCast)*
;

TypeCast infers Expr:
    TypeAsc ({infer TypeCast.expr=current} 'cast' 'as' type=Type)*
;

TypeAsc infers Expr:
    LogicAnd ({infer TypeAsc.expr=current} 'as' type=Type)*
;

LogicAnd infers Expr:
    LogicOr ({infer LogicAnd.left=current} 'and' right=LogicOr)*
;

LogicOr infers Expr:
    Subtract ({infer LogicOr.left=current} 'or' right=Subtract)*
;

Subtract infers Expr:
    Add ({infer Subtraction.left=current} '-' right=Add)*
;

Add infers Expr:
    Multiply ({infer Add.left=current} '+' right=Multiply)*
;

Multiply infers Expr:
    Divide ({infer Multiply.left=current} '*' right=Divide)*
;

Divide infers Expr:
    FuncApplicationOrDotSomething ({infer Divide.left=current} '/' right=FuncApplicationOrDotSomething)*
;

FuncApplicationOrDotSomething infers Expr:
    Primary (
          ({infer Application.fun=current} '(' (args+=Expr (',' args+=Expr)*)? ')')
        | ({infer TypeApplication.fun=current} '[' (types+=Type (',' types+=Type)*) ']')
        | '.' (
              {infer DotRecord.expr=current} label=ID
            | {infer DotTuple.expr=current} index=INT
        )
    )*
;


/** Non-left-recursive expressions */
Primary infers Expr:
    (
        ConstTrue
        | ConstFalse
        | ConstUnit
        | ConstInt
        | ConstMemory
        | Var
        | Panic
        | Throw
        | TryCatch
        | TryCastAs
        | TryWith
        | Inl
        | Inr
        | ConsList
        | Head
        | IsEmpty
        | Tail
        | Succ
        | LogicNot
        | Pred
        | IsZero
        | Fix
        | NatRec
        | Fold
        | Unfold
        | Ref
        | Deref
        | Abstraction
        | Tuple
        | Record
        | Variant
        | Match
        | List
        | If
        | Let
        | LetRec
        | TypeAbstraction
        | ParenthesisedExpr
    )
;


// Patterns

Pattern:
    PatternCastAs
;

PatternCastAs infers Pattern:
    PatternAsc ({infer PatternCastAs.pattern=current} 'cast' 'as' type=Type)*
;

PatternAsc infers Pattern:
    PrimaryPattern ({infer PatternAsc.pattern=current} 'as' type=Type)*
;

PatternBinding:
    pattern=Pattern '=' rhs=Expr;

Binding:
    name=ID '=' rhs=Expr;
PatternVariant:
    '<|' label=ID ('=' pattern=Pattern)? '|>';
PatternInl:
    'inl' '(' pattern=Pattern ')';
PatternInr:
    'inr' '(' pattern=Pattern ')';

PatternTuple:
    '{' (patterns+=Pattern (',' patterns+=Pattern)*)? '}';
PatternRecord:
    '{' (patterns+=LabelledPattern (',' patterns+=LabelledPattern)*)? '}';
PatternList:
    '[' (patterns+=Pattern (',' patterns+=Pattern)*)? ']';
PatternCons:
    // Legacy syntax did not require "cons"
    usesNewSyntax?='cons'? '(' head=Pattern ',' tail=Pattern ')';
PatternFalse:
    {infer PatternFalse} 'false';
PatternTrue:
    {infer PatternTrue} 'true';
PatternUnit:
    {infer PatternUnit} 'unit';
PatternInt:
    n=INT;
PatternSucc:
    'succ' '(' pattern=Pattern ')';
PatternVar:
    name=ID;
ParenthesisedPattern:
    '(' pattern=Pattern ')';

/** Patterns without left-recursion */
PrimaryPattern infers Pattern:
    PatternVariant
    | PatternInl
    | PatternInr
    | PatternTuple
    | PatternRecord
    | PatternList
    | PatternCons
    | PatternFalse
    | PatternTrue
    | PatternUnit
    | PatternInt
    | PatternSucc
    | PatternVar
    | ParenthesisedPattern;

LabelledPattern:
    label=ID '=' pattern=Pattern;

// Types

type TypeDecl = GenericTypeVar | DeclTypeAlias | TypeRec;

Type:
    TypeSum
;

TypeSum infers Type:
    PrimaryType ({infer TypeSum.left=current} '+' right=PrimaryType)*
;

TypeBool:
    {infer TypeBool} 'Bool';
TypeNat:
    {infer TypeNat} 'Nat';
TypeRef:
    '&' type=Type;
TypeFun:
    'fn' '(' (paramTypes+=Type (',' paramTypes+=Type)*)? ')' '->' returnType=Type;
TypeForAll:
    'forall' (types+=GenericTypeVar)* '.' type=Type;
TypeRec:
    'µ' name=ID '.' type=Type;
TypeTuple:
    '{' (types+=Type (',' types+=Type)*)? '}';
TypeRecord:
    '{' fieldTypes+=RecordFieldType (',' fieldTypes+=RecordFieldType)* '}';
RecordFieldType:
    label=ID ':' type=Type;
TypeVariant:
    '<|' (fieldTypes+=VariantFieldType (',' fieldTypes+=VariantFieldType)*)? '|>';
VariantFieldType:
    label=ID (':' type=Type)?;
TypeList:
    '[' type=Type ']'
    | 'List' '[' type=Type ']';
TypeUnit:
    {infer TypeUnit} 'Unit';
TypeTop:
    {infer TypeTop} 'Top';
TypeBottom:
    {infer TypeBottom} 'Bot';
TypeAuto:
    {infer TypeAuto} 'auto';
TypeVar:
    ref=[TypeDecl];
TypeParens:
    '(' type=Type ')';

/** Types without left-recursion */
PrimaryType:
    TypeBool
    | TypeNat
    | TypeRef
    | TypeFun
    | TypeForAll
    | TypeRec
    | TypeTuple
    | TypeRecord
    | TypeVariant
    | TypeList
    | TypeUnit
    | TypeTop
    | TypeBottom
    | TypeAuto
    | TypeVar
    | TypeParens;


hidden terminal WS: /\s+/;
terminal ID: /[_a-zA-Z][!\-:?\w]*/;
terminal EXTENSION_NAME: /#[-\w]+/;
terminal MEMORY_ADDRESS: /<0x[\da-fA-F]+>/;
terminal INT returns number: /[0-9]+/;
terminal STRING: /"(\\.|[^"\\])*"/;

hidden terminal ML_COMMENT: /\/\*[\s\S]*?\*\//;
hidden terminal SL_COMMENT: /\/\/[^\n\r]*/;
