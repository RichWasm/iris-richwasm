## Unannotated

```rust
enum Copyability {
  NoCopy,
  ExCopy,
  ImCopy,
}
enum Dropability {
  NoDrop,
  ExDrop,
  ImDrop,
}
enum Memory {
  MM,
  GC,
}
enum PrimitiveRep {
  Ptr,
  I32,
  I64,
  F32,
  F64,
}
enum Representation {
  Var(i64),
  Sum(List<Representation>),
  Prod(List<Representation>),
  Prim(PrimitiveRep),
}
enum Size {
  Var(i64),
  Sum(List<Size>),
  Prod(List<Size>),
  Rep(Representation),
  Const(i64),
}
enum Sizity {
  Sized(Size),
  UnSized,
}
enum Kind {
  VALTYPE(Representation, Copyability, Dropability),
  MEMTYPE(Sizity, Memory, Dropability),
}
enum Quantifier {
  Memory,
  Representation,
  Size,
  Type(Kind),
}
enum Sign {
  UnSigned,
  Signed,
}
enum IntType {
  I32,
  I64,
}
enum IntUnop {
  Clz,
  Ctz,
  Popcnt,
}
enum IntBinop {
  Add,
  Sub,
  Mul,
  Div(Sign),
  Rem(Sign),
  And,
  Or,
  Xor,
  Shl,
  Shr(Sign),
  Rotl,
  Rotr,
}
enum IntTestop {
  Eqz,
}
enum IntRelop {
  Eq,
  Ne,
  Lt(Sign),
  Gt(Sign),
  Le(Sign),
  Ge(Sign),
}
enum FloatType {
  F32,
  F64,
}
enum FloatUnop {
  Neg,
  Abs,
  Ceil,
  Floor,
  Trunc,
  Nearest,
  Sqrt,
}
enum FloatBinop {
  Add,
  Sub,
  Mul,
  Div,
  Min,
  Max,
  CopySign,
}
enum FloatRelop {
  Eq,
  Ne,
  Lt,
  Gt,
  Le,
  Ge,
}
enum NumType {
  Int(IntType),
  Float(FloatType),
}
enum ConversionOp {
  Wrap,
  Extend(Sign),
  Trunc(FloatType, IntType, Sign),
  Demote,
  Promote,
  Convert(IntType, FloatType, Sign),
  Reinterpret(NumType),
}
enum NumInstruction {
  Int1(IntType, IntUnop),
  Int2(IntType, IntBinop),
  IntTest(IntType, IntTestop),
  IntRel(IntType, IntRelop),
  Float1(FloatType, FloatUnop),
  Float2(FloatType, FloatBinop),
  FloatRel(FloatType, FloatRelop),
  Cvt(ConversionOp),
}
enum Type {
  Var(i64),
  I31,
  Num(NumType),
  Sum(List<Type>),
  Variant(List<Type>),
  Prod(List<Type>),
  Struct(List<Type>),
  Ref(Memory, Type),
  GCPtr(Type),
  CodeRef(FunctionType),
  Pad(Size, Type),
  Ser(Type),
  Rec(Type),
  Exists(Quantifier, Type),
}
enum FunctionType {
  FunctionType(List<Quantifier>, List<Type>, List<Type>),
}
enum BlockType {
  BlockType(List<Type>),
}
enum LocalFx {
  LocalFx(List<(i64, Type)>),
}
enum Index {
  Mem(Memory),
  Rep(Representation),
  Size(Size),
  Type(Type),
}
enum PathComponent {
  Proj(i64),
  Unwrap,
}
enum Path {
  Path(List<Component>),
}

enum Thing {
  Copy,
  Move
}
enum Instruction {
  Nop,
  Unreachable,
  Copy,
  Drop,
  Num(NumInstruction),
  NumConst(NumType, i64),
  Block(BlockType, LocalFx, List<Instruction>),
  Loop(BlockType, List<Instruction>),
  Ite(BlockType, LocalFx, List<Instruction>, List<Instruction>),
  Br(i64),
  Return,
  LocalGet(i64, Thing),
  LocalSet(i64),
  CodeRef(i64),
  Inst(Index),
  Call(i64, List<Index>),
  CallIndirect,
  Inject(Option<ConcreteMemory>, i64, List<Type>),
  Case(BlockType, LocalFx, List<List<Instruction>>),
  Group(i64),
  Ungroup,
  Fold(Type),
  Unfold,
  Pack(Index, Type),
  Unpack(BlockType, LocalFx, List<Instruction> // weakens
  ),
  Tag,
  Untag,
  New(ConcreteMemory, Type),
  Load(Path, Thing),
  Store(Path, Option<Type>),
  Swap(Path),
}
struct ModuleFunction {
  typ : FunctionType;
  locals : List<Representation>;
  body : List<Instruction>;
}

struct Module {
  imports : List<FunctionType>;
  functions : List<Function>;
  table : List<i64>;
  exports : List<i64>;
}
```

## Annotated
```rs
type PathComponent {
  PCProj(i64),
  PCSkip,
}
type Path = List<PathComponent>

enum ConcreteMemory {
  MemMM,
  MemGC,
}
enum Sign {
  SignU,
  SignS,
}
enum IntType {
  I32T,
  I64T,
}
enum FloatType {
  F32T,
  F64T,
}
enum NumType {
  IntT(IntType),
  FloatT(FloatType),
}
enum ConversionOp {
  CWrap,
  CExtend(Sign),
  CTrunc(FloatType, IntType, Sign),
  CDemote,
  CPromote,
  CConvert(IntType, FloatType, Sign),
  CReinterpret(NumType),
}
enum Copyability {
  NoCopy,
  ExCopy,
  ImCopy,
}
enum Dropability {
  NoDrop,
  ExDrop,
  ImDrop,
}
enum FloatBinop {
  AddF,
  SubF,
  MulF,
  DivF,
  MinF,
  MaxF,
  CopySignF,
}
enum FloatRelop {
  EqF,
  NeF,
  LtF,
  GtF,
  LeF,
  GeF,
}
enum FloatUnop {
  NegF,
  AbsF,
  CeilF,
  FloorF,
  TruncF,
  NearestF,
  SqrtF,
}
enum PrimitiveRep {
  PtrR,
  I32R,
  I64R,
  F32R,
  F64R,
}
enum Representation {
  VarR(i64),
  SumR(List<Representation>),
  ProdR(List<Representation>),
  PrimR(PrimitiveRep),
}
enum Size {
  VarS(i64),
  SumS(List<Size>),
  ProdS(List<Size>),
  RepS(Representation),
  ConstS(i64),
}
enum Memory {
  VarM(i64),
  ConstM(ConcreteMemory),
}
enum Sizity {
  Sized(Size),
  UnSized,
}
enum Kind {
  VALTYPE(Representation, Copyability, Dropability),
  MEMTYPE(Sizity, Memory, Dropability),
}
enum Type {
  VarT(i64),
  I31T(Kind),
  NumT(Kind, NumType),
  SumT(Kind, List<Type>),
  VariantT(Kind, List<Type>),
  ProdT(Kind, List<Type>),
  StructT(Kind, List<Type>),
  RefT(Kind, Memory, Type),
  GCPtrT(Kind, Type),
  CodeRefT(Kind, FunctionType),
  PadT(Kind, Size, Type),
  SerT(Kind, Type),
  RecT(Kind, Type),
  ExistsMemT(Kind, Type),
  ExistsRepT(Kind, Type),
  ExistsSizeT(Kind, Type),
  ExistsTypeT(Kind, Kind, Type),
}
enum FunctionType {
  MonoFunT(List<Type>, List<Type>),
  ForallMemT(FunctionType),
  ForallRepT(FunctionType),
  ForallSizeT(FunctionType),
  ForallTypeT(Kind, FunctionType),
}
enum Index {
  MemI(Memory),
  RepI(Representation),
  SizeI(Size),
  TypeI(Type),
}
enum IntUnop {
  ClzI,
  CtzI,
  PopcntI,
}
enum IntTestop {
  EqzI,
}
enum IntRelop {
  EqI,
  NeI,
  LtI(Sign),
  GtI(Sign),
  LeI(Sign),
  GeI(Sign),
}
enum IntBinop {
  AddI,
  SubI,
  MulI,
  DivI(Sign),
  RemI(Sign),
  AndI,
  OrI,
  XorI,
  ShlI,
  ShrI(Sign),
  RotlI,
  RotrI,
}
enum NumInstruction {
  IInt1(IntType, IntUnop),
  IInt2(IntType, IntBinop),
  IIntTest(IntType, IntTestop),
  IIntRel(IntType, IntRelop),
  IFloat1(FloatType, FloatUnop),
  IFloat2(FloatType, FloatBinop),
  IFloatRel(FloatType, FloatRelop),
  ICvt(ConversionOp),
}
enum InstructionType {
  InstrT(List<Type>, List<Type>),
}
enum Instruction {
  INop(InstructionType),
  IUnreachable(InstructionType),
  ICopy(InstructionType),
  IDrop(InstructionType),
  INum(InstructionType, NumInstruction),
  INumConst(InstructionType, i64),
  IBlock(InstructionType, List<Option<Type>>, List<Instruction>),
  ILoop(InstructionType, List<Instruction>),
  IIte(InstructionType, List<Option<Type>>, List<Instruction>, List<Instruction>)
  IBr(InstructionType, i64),
  IReturn(InstructionType),
  ILocalGet(InstructionType, i64),
  ILocalSet(InstructionType, i64),
  ICodeRef(InstructionType, i64),
  IInst(InstructionType, Index),
  ICall(InstructionType, i64, List<Index>),
  ICallIndirect(InstructionType),
  IInject(InstructionType, i64),
  ICase(InstructionType, List<Option<Type>>, List<List<Instruction>>),
  IGroup(InstructionType),
  IUngroup(InstructionType),
  IFold(InstructionType),
  IUnfold(InstructionType),
  IPack(InstructionType),
  IUnpack(InstructionType, List<Option<Type>>, List<Instruction>),
  ITag(InstructionType),
  IUntag(InstructionType),
  INew(InstructionType),
  ILoad(InstructionType, Path),
  IStore(InstructionType, Path),
  ISwap(InstructionType, Path),
}
struct ModuleFunction {
  mf_type : FunctionType;
  mf_locals : List<Representation>;
  mf_body : List<Instruction>;
}

struct Module {
  m_imports : List<FunctionType>;
  m_functions : List<ModuleFunction>;
  m_table : List<i64>;
  m_exports : List<i64>
}
```
