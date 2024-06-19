Require Import CoqOfPython.CoqOfPython.
Require Import simulations.CoqOfPython.
Require Import simulations.builtins.

Import simulations.CoqOfPython.Notations.

Definition globals : Globals.t := "ethereum.base_types".

Definition U255_CEIL_VALUE : Z := 2^255.

Definition U256_CEIL_VALUE : Z := 2^256.

(* NOTE: Python built-in type. We put here for convenience. *)
Definition bytearray := list ascii.

(* NOTE: A byte should consist of 2 hex digits or 4 binary digits
  https://docs.python.org/3/library/stdtypes.html#bytes *)
Module FixedBytes.
  Inductive t : Set :=
  | Make (bytes : list ascii).
  (* NOTE: some draft that might be useful for future extension
  Inductive ByteOrder := 
  | LittleEndian
  | BigEndian
  *)
  (* Make (bytes: list ascii) (signed : bool) (byte_order : ByteOrder) *)

  Definition get (bytes : t) : list ascii :=
    match bytes with
    | Make bytes => bytes
    end.
End FixedBytes.

(* TODO: Make some consistent definitions in the following modules:
- to_Uint: Apart from U_ series of modules, we might also need its def for FixedUint
- bytearray, FixedBytes & Bytes: also define a consistent covert functions between them
*)

Module Uint.
(* NOTE: to_bytes would produce a list of byte with *undetermined* length
*)
  Inductive t : Set :=
  | Make (value : Z).

  Definition get (value : t) : Z :=
    match value with
    | Make value => value
    end.

  Definition __add__ (self right_ : t) : t :=
    Make (get self + get right_).

  (* NOTE: Currently for convenience we only define "from fixedbytes to uint" 
           An ideal translation should go from fixedbytes -> bytes -> uint *)
  (* TODO: Distinguish between `from_be_bytes` and `from_le_bytes` *)
  (* 
    def from_bytes(bytes, byteorder='big', signed=False):
      if byteorder == 'little':
          little_ordered = list(bytes)
      elif byteorder == 'big':
          little_ordered = list(reversed(bytes))
      else:
          raise ValueError("byteorder must be either 'little' or 'big'")

      n = sum(b << i*8 for i, b in enumerate(little_ordered))
      if signed and little_ordered and (little_ordered[-1] & 0x80):
          n -= 1 << 8*len(little_ordered)

      return n
  *)
  (* 
    NOTE:
    - Currently we don't support between different endians
    - From definition of related functions(?), it seems that `little_ordered` 
      doesnt have a fixed length or even length of multiples of 2
      (Question: Does Python check the length of byte array?)
  *)
  Fixpoint from_bytes_helper (bytes : list ascii) (store : Z) : Z :=
    match bytes with
    | [] => 0
    | (b::bs) => from_bytes_helper bs ((Z_of_N (N_of_ascii b)) * 8 + store)
    end.

  Definition from_bytes (bytes : FixedBytes.t) : t :=
    let '(FixedBytes.Make little_ordered) := bytes in
    let result := from_bytes_helper little_ordered 0 in
    (* NOTE: last_byte provides a default value 0 *)
    let z0 := List.last little_ordered (ascii_of_N 0) in
    let z1 := Z.of_N (N_of_ascii z0) in
    let ascii_xor_result := Z.land z1 0x80 in
    Make (
      if ascii_xor_result =? 0
      then result - Z.shiftl 1 (Z_of_nat (List.length little_ordered))
      else result).
End Uint.

Module FixedUint.
  Record t : Set := {
    MAX_VALUE : Z;
    value : Z;
  }.

  Definition __add__ (self right_ : t) : M? Exception.t t :=
    let result := (self.(value) + right_.(value))%Z in
    if result >? self.(MAX_VALUE) then
      Error.raise (Exception.ArithmeticError ArithmeticError.OverflowError)
    else
      return? {|
        MAX_VALUE := self.(MAX_VALUE);
        value := result;
      |}.

  Definition wrapping_add (self right_ : t) : t :=
    let sum := (self.(value) + right_.(value))%Z in
    {|
      MAX_VALUE := self.(MAX_VALUE);
      value := Z.modulo sum self.(MAX_VALUE);
    |}.
  
  Definition __sub__ (self right_ : t) : M? Exception.t t :=
    let result := (self.(value) - right_.(value))%Z in
    if result >? self.(MAX_VALUE) then
      Error.raise (Exception.ArithmeticError ArithmeticError.OverflowError)
    else
      return? {|
        MAX_VALUE := self.(MAX_VALUE);
        value := result;
      |}.

  Definition wrapping_sub (self right_ : t) : t :=
    let sub := (self.(value) - right_.(value))%Z in
    {|
      MAX_VALUE := self.(MAX_VALUE);
      value := Z.modulo sub self.(MAX_VALUE);
    |}.

  Definition __mul__ (self right_ : t) : M? Exception.t t :=
    let result := (self.(value) * right_.(value))%Z in
    if result >? self.(MAX_VALUE) then
      Error.raise (Exception.ArithmeticError ArithmeticError.OverflowError)
    else
      return? {|
        MAX_VALUE := self.(MAX_VALUE);
        value := result;
      |}.

  Definition wrapping_mul (self right_ : t) : t :=
    let mul := (self.(value) * right_.(value))%Z in
    {|
      MAX_VALUE := self.(MAX_VALUE);
      value := Z.modulo mul self.(MAX_VALUE);
    |}.

  Definition bit_and (self right_ : t) : t :=
    let x := self.(value)%Z in
    let y := right_.(value)%Z in
    {|
      MAX_VALUE := self.(MAX_VALUE);
      value := Z.land x y;
    |}.

  Definition bit_or (self right_ : t) : t :=
    let x := self.(value)%Z in
    let y := right_.(value)%Z in
    {|
      MAX_VALUE := self.(MAX_VALUE);
      value := Z.lor x y;
    |}.

  Definition bit_xor (self right_ : t) : t :=
    let x := self.(value)%Z in
    let y := right_.(value)%Z in
    {|
      MAX_VALUE := self.(MAX_VALUE);
      value := Z.lxor x y;
    |}.

  Definition bit_not (self : t) : t :=
    let x := self.(value)%Z in
    {|
      MAX_VALUE := self.(MAX_VALUE);
      value := Z.lnot x;
    |}.

  Definition to_Uint (self : t) : Uint.t :=
    let x := self.(value)%Z in Uint.Make x.
End FixedUint.

Module U256.
  Inductive t : Set :=
  | Make (value : FixedUint.t).

  Definition of_Z (value : Z) : t :=
    Make {|
      FixedUint.MAX_VALUE := 2^256 - 1;
      FixedUint.value := value;
    |}.

  Definition get (value : t) : FixedUint.t :=
    let 'Make value := value in
    value.

  Definition to_Z (value : t) : Z :=
    FixedUint.value (get value).

  Definition to_value (value : t) : Value.t :=
    Value.Make globals "U256" (Pointer.Imm (Object.wrapper (Data.Integer (to_Z value)))).

  Definition MAX_VALUE : t := U256.of_Z (2^256 - 1).

  Definition __add__ (self right_ : t) : M? Exception.t t :=
    let? result := FixedUint.__add__ (get self) (get right_) in
    return? (Make result).

  Definition wrapping_add (self right_ : t) : t :=
    Make (FixedUint.wrapping_add (get self) (get right_)).

  Definition __sub__ (self right_ : t) : M? Exception.t t :=
    let? result := FixedUint.__sub__ (get self) (get right_) in
    return? (Make result).

  Definition wrapping_sub (self right_ : t) : t :=
    Make (FixedUint.wrapping_sub (get self) (get right_)).

  Definition __mul__ (self right_ : t) : M? Exception.t t :=
    let? result := FixedUint.__mul__ (get self) (get right_) in
    return? (Make result).

  Definition wrapping_mul (self right_ : t) : t :=
    Make (FixedUint.wrapping_mul (get self) (get right_)).

  Definition bit_and (self right_ : t) : t :=
    Make (FixedUint.bit_and (get self) (get right_)).

  Definition bit_or (self right_ : t) : t :=
    Make (FixedUint.bit_or (get self) (get right_)).

  Definition bit_xor (self right_ : t) : t :=
    Make (FixedUint.bit_xor (get self) (get right_)).

  Definition bit_not (self : t) : t :=
    Make (FixedUint.bit_not (get self)).
  (*  
  def from_signed(cls: Type, value: int) -> "U256":
      """
      Creates an unsigned integer representing `value` using two's
      complement.
      """
      if value >= 0:
          return cls(value)

      return cls(value & cls.MAX_VALUE)
  *)  
  (* NOTE: for now we ignore the cls here *)  
  Definition from_signed (self : t) : t :=
    let value := U256.to_Z self in
    if value >=? 0 
    then (U256.of_Z value)
    (* TODO: here 2^256 - 1 should be the max value of the corresponded class.
       To be modified in the future. *)
    else (U256.of_Z (Z.land value (2^256 - 1))).

  Definition to_Uint (self : t) : Uint.t :=
    let '(Make x) := self in FixedUint.to_Uint x.
End U256.

Module U32.
  Inductive t : Set :=
  | Make (value : FixedUint.t).

  Definition of_Z (value : Z) : t :=
    Make {|
      FixedUint.MAX_VALUE := 2^32 - 1;
      FixedUint.value := value;
    |}.

  Definition get (value : t) : FixedUint.t :=
    match value with
    | Make value => value
    end.
End U32.

Module U64.
  Inductive t : Set :=
  | Make (value : FixedUint.t).

  Definition of_Z (value : Z) : t :=
    Make {|
      FixedUint.MAX_VALUE := 2^64 - 1;
      FixedUint.value := value;
    |}.

  Definition get (value : t) : FixedUint.t :=
    match value with
    | Make value => value
    end.

  Definition to_Uint (self : t) : Uint.t :=
    let '(Make value) := self in 
      FixedUint.to_Uint value.
End U64.

Module Bytes0.
  Inductive t : Set :=
  | Make (bytes : FixedBytes.t).

  Definition get (bytes : t) : FixedBytes.t :=
    match bytes with
    | Make bytes => bytes
    end.
End Bytes0.

Module Bytes4.
  Inductive t : Set :=
  | Make (bytes : FixedBytes.t).

  Definition get (bytes : t) : FixedBytes.t :=
    match bytes with
    | Make bytes => bytes
    end.
End Bytes4.

Module Bytes8.
  Inductive t : Set :=
  | Make (bytes : FixedBytes.t).

  Definition get (bytes : t) : FixedBytes.t :=
    match bytes with
    | Make bytes => bytes
    end.
End Bytes8.

Module Bytes20.
  Inductive t : Set :=
  | Make (bytes : FixedBytes.t).

  Definition get (bytes : t) : FixedBytes.t :=
    match bytes with
    | Make bytes => bytes
    end.
End Bytes20.

Module Bytes32.
  Inductive t : Set :=
  | Make (bytes : FixedBytes.t).

  Definition get (bytes : t) : FixedBytes.t :=
    match bytes with
    | Make bytes => bytes
    end.

  Definition LENGTH := 32.
End Bytes32.

Module Bytes48.
  Inductive t : Set :=
  | Make (bytes : FixedBytes.t).

  Definition get (bytes : t) : FixedBytes.t :=
    match bytes with
    | Make bytes => bytes
    end.
End Bytes48.

Module Bytes64.
  Inductive t : Set :=
  | Make (bytes : FixedBytes.t).

  Definition get (bytes : t) : FixedBytes.t :=
    match bytes with
    | Make bytes => bytes
    end.
End Bytes64.

Module Bytes256.
  Inductive t : Set :=
  | Make (bytes : FixedBytes.t).

  Definition get (bytes : t) : FixedBytes.t :=
    match bytes with
    | Make bytes => bytes
    end.
End Bytes256.

Module Bytes.
  Inductive t : Set :=
  | Make (bytes : list ascii).

  Definition get (bytes : t) : list ascii :=
    match bytes with
    | Make bytes => bytes
    end.
End Bytes.
