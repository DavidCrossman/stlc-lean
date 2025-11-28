namespace Stlc

structure Config : Type where
  hasBool : Bool
deriving DecidableEq

namespace Config

class HasBool (c : Config) : Prop where
  hasBool : c.hasBool
deriving DecidableEq

instance : HasBool { hasBool := true } :=
  { hasBool := rfl }

end Config

instance : DecidablePred Config.HasBool := fun c ↦
  decidable_of_bool c.hasBool ⟨fun h ↦ { hasBool := h }, fun h ↦ h.hasBool⟩

def TermVar : Type := String
deriving DecidableEq

inductive Ty (c : Config) : Type
| bool [c.HasBool] : Ty c
| arrow : Ty c → Ty c → Ty c
deriving DecidableEq

inductive Term (c : Config) : Type
| var : TermVar → Term c
| abs : TermVar → Ty c → Term c → Term c
| app : Term c → Term c → Term c
| bool [c.HasBool] : Bool → Term c
| ite [c.HasBool] : Term c → Term c → Term c → Term c
deriving DecidableEq

end Stlc
