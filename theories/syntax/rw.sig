list : Functor

nat : Type

linearity : Type
Lin : linearity
Unr : linearity

memory (MemVar) : Type
MemMM : memory
MemGC : memory

primitive_rep : Type
PtrR : primitive_rep
I32R : primitive_rep
I64R : primitive_rep
F32R : primitive_rep
F64R : primitive_rep

representation (VarR) : Type
SumR : "list" (representation) -> representation
ProdR : "list" (representation) -> representation
PrimR : primitive_rep -> representation

size (VarS) : Type
SumS : "list" (size) -> size
ProdS : "list" (size) -> size
RepS : representation -> size
ConstS : nat -> size

sizity : Type
Sized : size -> sizity
Unsized : sizity

kind : Type
VALTYPE : representation -> linearity -> kind
MEMTYPE : sizity -> memory -> linearity -> kind

int_type : Type
I32T : int_type
I64T : int_type

float_type : Type
F32T : float_type
F64T : float_type

num_type : Type
IntT : int_type -> num_type
FloatT : float_type -> num_type

type (VarT) : Type
NumT : kind -> num_type -> type
SumT : kind -> "list" (type) -> type
ProdT : kind -> "list" (type) -> type
ArrayT : kind -> type -> type
RefT : kind -> memory -> type
GCPtrT : kind -> type -> type
CodeRefT : kind -> function_type -> type
RepT : kind -> representation -> type -> type
PadT : kind -> size -> type -> type
SerT : kind -> type -> type
RecT : kind -> (bind type in type) -> type
ExMemT : kind -> (bind memory in type) -> type
ExRepT : kind -> (bind representation in type) -> type
ExSizeT : kind -> (bind size in type) -> type
ExTypeT : kind -> (bind type in type) -> type

arrow_type : Type
ArrowT : "list" (type) -> "list" (type) -> arrow_type

function_type : Type
FaMemT : (bind memory in function_type) -> function_type
FaRepT : (bind representation in function_type) -> function_type
FaSizeT : (bind size in function_type) -> function_type
FaTypeT : kind -> (bind type in function_type) -> function_type
FunT : arrow_type -> function_type

local_ctx : Type
LocalCtx : "list" (type) -> local_ctx

index : Type
MemI : memory -> index
RepI : representation -> index
SizeI : size -> index
TypeI : type -> index

sign : Type
SignU : sign
SignS : sign

path_component : Type
PCProj : nat -> path_component
PCUnwrap : path_component

path : Type
Path : "list" (path_component) -> path

int_unop : Type
ClzI : int_unop
CtzI : int_unop
PopcntI : int_unop

int_binop : Type
AddI : int_binop
SubI : int_binop
MulI : int_binop
DivI : sign -> int_binop
RemI : sign -> int_binop
AndI : int_binop
OrI : int_binop
XorI : int_binop
ShlI : int_binop
ShrI : sign -> int_binop
RotlI : int_binop
RotrI : int_binop

int_testop : Type
EqzI : int_testop

int_relop : Type
EqI : int_relop
NeI : int_relop
LtI : sign -> int_relop
GtI : sign -> int_relop
LeI : sign -> int_relop
GeI : sign -> int_relop

float_unop : Type
NegF : float_unop
AbsF : float_unop
CeilF : float_unop
FloorF : float_unop
TruncF : float_unop
NearestF : float_unop
SqrtF : float_unop

float_binop : Type
AddF : float_binop
SubF : float_binop
MulF : float_binop
DivF : float_binop
MinF : float_binop
MaxF : float_binop
CopySignF : float_binop

float_relop : Type
EqF : float_relop
NeF : float_relop
LtF : float_relop
GtF : float_relop
LeF : float_relop
GeF : float_relop

conversion_op : Type
CWrap : conversion_op
CExtend : sign -> conversion_op
CTrunc : int_type -> float_type -> sign -> conversion_op
CTruncSat : int_type -> float_type -> sign -> conversion_op
CDemote : conversion_op
CPromote : conversion_op
CConvert : float_type -> int_type -> sign -> conversion_op
CReinterpretFI : float_type -> int_type -> conversion_op
CReinterpretIF : int_type -> float_type -> conversion_op
CReinterpretII : int_type -> sign -> sign -> conversion_op

num_instruction : Type
IInt1 : int_type -> int_unop -> num_instruction
IInt2 : int_type -> int_binop -> num_instruction
IIntTest : int_type -> int_testop -> num_instruction
IIntRel : int_type -> int_relop -> num_instruction
IFloat1 : float_type -> float_unop -> num_instruction
IFloat2 : float_type -> float_binop -> num_instruction
IFloatRel : float_type -> float_relop -> num_instruction
ICvt : conversion_op -> num_instruction

instruction : Type
INop : type -> instruction
IDrop : type -> instruction
IUnreachable : type -> instruction
INum : type -> num_instruction -> instruction
INumConst : type -> num_type -> nat -> instruction
IBlock : type -> arrow_type -> local_ctx -> "list" (instruction) -> instruction
ILoop : type -> arrow_type -> "list" (instruction) -> instruction
IIte : type -> arrow_type -> local_ctx -> "list" (instruction) -> "list" (instruction) -> instruction
IBr : type -> nat -> instruction
IBrIf : type -> nat -> instruction
IReturn : type -> instruction
ILocalGet : type -> nat -> instruction
ILocalSet : type -> nat -> instruction
IGlobalGet : type -> nat -> instruction
IGlobalSet : type -> nat -> instruction
ICodeRef : type -> nat -> instruction
IInst : type -> index -> instruction
ICall : type -> nat -> "list" (index) -> instruction
ICallIndirect : type -> instruction
IGroup : type -> nat -> instruction
IUngroup : type -> instruction
IFold : type -> type -> instruction
IUnfold : type -> instruction
IPack : type -> kind -> index -> instruction
IUnpack : type -> arrow_type -> local_ctx -> "list" (instruction) -> instruction
IWrap : type -> instruction
IUnwrap : type -> instruction
IRefNew : type -> memory -> instruction
IRefFree : type -> instruction
IRefDup : type -> instruction
IRefDrop : type -> instruction
IRefLoad : type -> path -> instruction
IRefStore : type -> path -> instruction
IRefSwap : type -> path -> instruction
IVariantNew : type -> nat -> "list" (type) -> memory -> instruction
IVariantCase : type -> linearity -> arrow_type -> local_ctx -> "list" ("list" (instruction)) -> instruction
IArrayNew : type -> memory -> instruction
IArrayFree : type -> instruction
IArrayGet : type -> instruction
IArraySet : type -> instruction
