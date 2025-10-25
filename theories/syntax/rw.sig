nat : Type

list : Functor
prod : Functor
option : Functor

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

kind : Type
VALTYPE : representation -> copyability -> dropability -> kind
MEMTYPE : size -> dropability -> kind

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
I31T : kind -> type
NumT : kind -> num_type -> type
SumT : kind -> "list" (type) -> type
VariantT : kind -> "list" (type) -> type
ProdT : kind -> "list" (type) -> type
StructT : kind -> "list" (type) -> type
RefT : kind -> memory -> type -> type
CodeRefT : kind -> function_type -> type
SerT : kind -> type -> type
UninitT : kind -> size -> type
RecT : kind -> (bind type in type) -> type
ExistsMemT : kind -> (bind memory in type) -> type
ExistsRepT : kind -> (bind representation in type) -> type
ExistsSizeT : kind -> (bind size in type) -> type
ExistsTypeT : kind -> kind -> (bind type in type) -> type

function_type : Type
MonoFunT : "list" (type) -> "list" (type) -> function_type
ForallMemT : (bind memory in function_type) -> function_type
ForallRepT : (bind representation in function_type) -> function_type
ForallSizeT : (bind size in function_type) -> function_type
ForallTypeT : kind -> (bind type in function_type) -> function_type

instruction_type : Type
InstrT : "list" (type) -> "list" (type) -> instruction_type

index : Type
MemI : memory -> index
RepI : representation -> index
SizeI : size -> index
TypeI : type -> index

sign : Type
SignU : sign
SignS : sign

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
CTrunc : float_type -> int_type -> sign -> conversion_op
CDemote : conversion_op
CPromote : conversion_op
CConvert : int_type -> float_type -> sign -> conversion_op
CReinterpret : num_type -> conversion_op

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
INop : instruction_type -> instruction
IUnreachable : instruction_type -> instruction
ICopy : instruction_type -> instruction
IDrop : instruction_type -> instruction
INum : instruction_type -> num_instruction -> instruction
INumConst : instruction_type -> nat -> instruction
IBlock : instruction_type -> "list" ("option" (type)) -> "list" (instruction) -> instruction
ILoop : instruction_type -> "list" (instruction) -> instruction
IIte : instruction_type -> "list" ("option" (type)) -> "list" (instruction) -> "list" (instruction) -> instruction
IBr : instruction_type -> nat -> instruction
IReturn : instruction_type -> instruction
ILocalGet : instruction_type -> nat -> instruction
ILocalSet : instruction_type -> nat -> instruction
ICodeRef : instruction_type -> nat -> instruction
IInst : instruction_type -> index -> instruction
ICall : instruction_type -> nat -> "list" (index) -> instruction
ICallIndirect : instruction_type -> instruction
IInject : instruction_type -> nat -> instruction
ICase : instruction_type -> "list" ("option" (type)) -> "list" ("list" (instruction)) -> instruction
IGroup : instruction_type -> instruction
IUngroup : instruction_type -> instruction
IFold : instruction_type -> instruction
IUnfold : instruction_type -> instruction
IPack : instruction_type -> instruction
IUnpack : instruction_type -> "list" ("option" (type)) -> "list" (instruction) -> instruction
ITag : instruction_type -> instruction
IUntag : instruction_type -> instruction
ICast : instruction_type -> instruction
INew : instruction_type -> instruction
ILoad : instruction_type -> "list" (nat) -> instruction
IStore : instruction_type -> "list" (nat) -> instruction
ISwap : instruction_type -> "list" (nat) -> instruction
