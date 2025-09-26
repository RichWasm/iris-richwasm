type copyability = NoCopy | ExCopy | ImCopy

type dropability = NoDrop | ExDrop | ImDrop

type memory = MM | GC

type primitive_rep =
  | Ptr
  | I32
  | I64
  | F32
  | F64

type representation =
  | Var of int
  | Sum of representation list
  | Prod of representation list
  | Prim of primitive_rep

type size =
  | Var of int
  | Sum of size list
  | Prod of size list
  | Rep of representation
  | Const of int

type sizity =
  | Sized of size
  | Unsized

type kind =
  | VALTYPE of representation * copyability * dropability
  | MEMTYPE of sizity * memory * dropability

type quantifier =
  | Memory
  | Representation
  | Size
  | Type of kind

type int_type = I32 | I64

type float_type = F32 | F64

type num_type =
  | Int of int_type
  | Float of float_type

type typ =
  | Var of int
  | Num of num_type
  | Sum of typ list
  | Prod of typ list
  | Ref of memory * typ
  | GCPtr of typ
  | CodeRef of function_type
  | Rep of representation * typ
  | Pad of size * typ
  | Ser of typ
  | Rec of typ
  | Exists of quantifier * typ
and instruction_type = InstructionType of typ list * typ list
and function_type = FunctionType of quantifier list * instruction_type

type index =
  | Mem of memory
  | Rep of representation
  | Size of size
  | Type of typ

type local_fx = LocalFx of (int * typ) list

type sign = Unsigned | Signed

type int_unop = Clz | Ctz | Popcnt

type int_binop = Add | Sub | Mul | Div | Rem | And | Or | Xor | Shl | Shr | Rotl | Rotr

type int_testop = Eqz

type int_relop = Eq | Ne | Lt | Gt | Le | Ge

type float_unop = Neg | Abs | Ceil | Floor | Trunc | Nearest | Sqrt

type float_binop = Add | Sub | Mul | Div | Min | Max | CopySign

type float_relop = Eq | Ne | Lt | Gt | Le | Ge

type conversion_op =
  | Wrap
  | Extend of sign
  | Trunc of int_type * float_type * sign
  | TruncSat of int_type * float_type * sign
  | Demote
  | Promote
  | Convert of float_type * int_type * sign
  | ReinterpretFI of float_type * int_type
  | ReinterpretIF of int_type * float_type
  | ReinterpretII of int_type * sign * sign

type num_instruction =
  | Int1 of int_type * int_unop
  | Int2 of int_type * int_binop
  | IntTest of int_type * int_testop
  | IntRel of int_type * int_relop
  | Float1 of float_type * float_unop
  | Float2 of float_type * float_binop
  | FloatRel of float_type * float_relop
  | Cvt of conversion_op

type path_component =
  | Proj of int
  | Unwrap

type path = Path of path_component list

type instruction =
  | Nop
  | Unreachable
  | Copy
  | Drop
  | Num of num_instruction
  | NumConst of num_type * int
  | Block of instruction_type * local_fx * instruction list
  | Loop of instruction_type * instruction list
  | Ite of instruction_type * local_fx * instruction list * instruction list
  | Br of int
  | BrIf of int
  | BrTable of int list * int
  | Return
  | LocalGet of int
  | LocalSet of int
  | GlobalGet of int
  | GlobalSet of int
  | GlobalSwap of int
  | CodeRef of int
  | Inst of index
  | Call of int * index list
  | CallIndirect
  | Inject of int * typ list
  | Case of instruction_type * local_fx * instruction list list
  | Group of int
  | Ungroup
  | Fold of typ
  | Unfold
  | Pack of index * typ
  | Unpack of instruction_type * local_fx * instruction list
  | Wrap of typ
  | Unwrap
  | RefNew of memory * typ
  | RefLoad of path * typ
  | RefStore of path
  | RefSwap of path

type mutability = Mut | Imm

type module_import_desc =
  | ImFunction of function_type
  | ImGlobal of mutability * typ

type module_import =
  {
    name : string;
    desc : module_import_desc;
  }

type module_global =
  {
    mut : mutability;
    typ : typ;
    init : instruction list;
  }

type module_function =
  {
    typ : function_type;
    locals : representation list;
    body : instruction list;
  }

type module_export_desc =
  | ExFunction of int
  | ExGlobal of int

type module_export =
  {
    name : string;
    desc : module_export_desc;
  }

type modul =
  {
    imports : module_import list;
    globals : module_global list;
    functions : module_function list;
    table : int list;
    start : int option;
    exports : module_export list;
  }
