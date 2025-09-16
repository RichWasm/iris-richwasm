nat : Type
path : Type

list : Functor
prod : Functor

copyability : Type
NoCopy : copyability
ExCopy : copyability
ImCopy : copyability

dropability : Type
NoDrop : dropability
ExDrop : dropability
ImDrop : dropability

concrete_memory : Type
MemMM : concrete_memory
MemGC : concrete_memory

memory (VarM) : Type
ConstM : concrete_memory -> memory

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
VALTYPE : representation -> copyability -> dropability -> kind
MEMTYPE : sizity -> memory -> dropability -> kind

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
ArrT : kind -> type -> type
RefT : kind -> memory -> type -> type
GCPtrT : kind -> type -> type
CodeRefT : kind -> function_type -> type
RepT : kind -> representation -> type -> type
PadT : kind -> size -> type -> type
SerT : kind -> type -> type
RecT : kind -> (bind type in type) -> type
ExMemT : kind -> (bind memory in type) -> type
ExRepT : kind -> (bind representation in type) -> type
ExSizeT : kind -> (bind size in type) -> type
ExTypeT : kind -> kind -> (bind type in type) -> type

arrow_type : Type
ArrowT : "list" (type) -> "list" (type) -> arrow_type

function_type : Type
FaMemT : (bind memory in function_type) -> function_type
FaRepT : (bind representation in function_type) -> function_type
FaSizeT : (bind size in function_type) -> function_type
FaTypeT : kind -> (bind type in function_type) -> function_type
FunT : arrow_type -> function_type

index : Type
MemI : memory -> index
RepI : representation -> index
SizeI : size -> index
TypeI : type -> index

sign : Type
SignU : sign
SignS : sign

local_fx : Type
LocalFx : "list" ("prod" (nat, type)) -> local_fx

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
INop : arrow_type -> instruction
IUnreachable : arrow_type -> instruction
ICopy : arrow_type -> instruction
IDrop : arrow_type -> instruction
INum : arrow_type -> num_instruction -> instruction
INumConst : arrow_type -> nat -> instruction
IBlock : arrow_type -> local_fx -> "list" (instruction) -> instruction
ILoop : arrow_type -> "list" (instruction) -> instruction
IIte : arrow_type -> local_fx -> "list" (instruction) -> "list" (instruction) -> instruction
IBr : arrow_type -> nat -> instruction
IBrIf : arrow_type -> nat -> instruction
IBrTable : arrow_type -> "list" (nat) -> nat -> instruction
IReturn : arrow_type -> instruction
ILocalGet : arrow_type -> nat -> instruction
ILocalSet : arrow_type -> nat -> instruction
IGlobalGet : arrow_type -> nat -> instruction
IGlobalSet : arrow_type -> nat -> instruction
IGlobalSwap : arrow_type -> nat -> instruction
ICodeRef : arrow_type -> nat -> instruction
IInst : arrow_type -> index -> instruction
ICall : arrow_type -> nat -> "list" (index) -> instruction
ICallIndirect : arrow_type -> instruction
IInject : arrow_type -> nat -> instruction
ICase : arrow_type -> local_fx -> "list" ("list" (instruction)) -> instruction
IGroup : arrow_type -> instruction
IUngroup : arrow_type -> instruction
IFold : arrow_type -> instruction
IUnfold : arrow_type -> instruction
IPack : arrow_type -> instruction
IUnpack : arrow_type -> local_fx -> "list" (instruction) -> instruction
IWrap : arrow_type -> instruction
IUnwrap : arrow_type -> instruction
IRefNew : arrow_type -> instruction
IRefLoad : arrow_type -> path -> instruction
IRefStore : arrow_type -> path -> instruction
IRefSwap : arrow_type -> path -> instruction
IArrayNew : arrow_type -> instruction
IArrayGet : arrow_type -> instruction
IArraySet : arrow_type -> instruction
