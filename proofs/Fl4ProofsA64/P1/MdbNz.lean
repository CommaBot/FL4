/-
P1 (aarch64, gen 49): **`h0` from `OSOK`** — the case hypothesis "no `OS` slot at address 0" of gen 47/48 discharged
by the new `OSOK` field `nz` (Architect ruling: placement fact in `OSOK`, same layer as `TcbPlaced`; established at
boot and by retype, which grow `OS`; no other step changes `OS`).

* `OSOK.h0`: the field in `h0`'s form.
* **`vspace.decode_page_table.unmapRO`**: gen 47's `unmapRF` without `h0` (ARMPageTableUnmap of a mapped
  `PageTable` cap with `hone` from `MdbLk ∧ RngOneA64 ∧ KindA`); `hone_of_finalO`, `is_final.false_nmO`.
* `cdt.empty_slot.mdbO`, `cdt.cap_swap_for_delete.mdbO`, `cdt.insert_with_cap.mdbO`, `cdt.insert.mdbO`: gen 49's
  `…mdbN` lemmas (MdbNull) without `h0`.

Premise diff: `OSOK` gains the field `nz`, so the [J] entry facts that assert `OSOK` (`SlotTyEnt` and its widenings)
now also assert it; no new named premise.
-/
import Fl4ProofsA64.P1.MdbNull
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-- **`h0` from the placement**: no `OS` slot at address 0. -/
theorem OSOK.h0 {OS : Set U64} (hO : OSOK T Ω Sg OS) : ∀ y ∈ OS, y ≠ 0#u64 := hO.nz

section fin
variable {OS : Set U64} {G : List (List U64)}

/-- `is_final.false_nm` with `h0` from `OSOK`. -/
theorem is_final.false_nmO (hO : OSOK T Ω Sg OS) {s : S} (hM : MdbLk st OS G s) (hRO : RngOneA64 st G s)
    (hK : KindA st OS s) {x ptr : U64} {m : Bool} {a v : U64} (hx : x ∈ OS)
    (hc : obj.Slot.cap st x s = ok (.PageTable ptr m a v)) {y : U64} (hy : y ∈ OS) (hne : y ≠ x)
    (hn : NmC st y ptr s) : cdt.is_final_capability st s x = ok false :=
  is_final.false_nm hM hRO hK hO.nz hx hc hy hne hn

/-- `hone_of_final` with `h0` from `OSOK`. -/
theorem hone_of_finalO (hO : OSOK T Ω Sg OS) {s : S} (hM : MdbLk st OS G s) (hRO : RngOneA64 st G s)
    (hK : KindA st OS s) {x ptr : U64} {m : Bool} {a v : U64} (hx : x ∈ OS)
    (hc : obj.Slot.cap st x s = ok (.PageTable ptr m a v)) (hfin : cdt.is_final_capability st s x = ok true) :
    ∀ y ∈ OS, y ≠ x → ¬ NmC st y ptr s :=
  hone_of_final hM hRO hK hO.nz hx hc hfin

end fin

section dec
variable {OS Vc Ub : Set U64} {kb n : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A} {G : List (List U64)}

/-- **ARMPageTableUnmap of a mapped `PageTable` cap, `hone` and `h0` discharged**: gen 47's `unmapRF` with `h0`
from `OSOK.nz`. -/
theorem vspace.decode_page_table.unmapRO (hA : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hk : L.ksb s = kb) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    (hTe : Gran Te bits ⊆ Pt) (hH : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hY : VsTyR st kb Pp Hr Tb Lv s) (h2 : S2TyR st hPl.ipa Pp Hr Te Re bits s)
    (hU : UnmZ st OS Pt (S2Rt st Pp Te Re bits s) bits s) (hT : UnmT st OS (VsRt st Pp Hr Tb Lv s) s)
    (hV : UnmU st OS Pp s)
    (hM : MdbLk st OS G s) (hRO : RngOneA64 st G s) (hK : KindA st OS s)
    (a : A) (len slot buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) {ptr masid mvaddr : U64}
    (hsl : slot ∈ OS) (hc : obj.Slot.cap st slot s = ok (.PageTable ptr true masid mvaddr))
    (hF : PtFnd st hPl.ipa Pp Hr Lv Re bits s masid mvaddr ptr)
    (hptr : ptr ∈ Pt) (hal : Aligned ptr) (hfit : ptr.val + 4096 ≤ 2 ^ 64)
    (hD2 : ∀ q ∈ Te, q ≠ ptr → ∀ o o' : U64, o.val < 4096 → o.val % 8 = 0 → o'.val < 2 ^ bits q →
      o'.val % 8 = 0 → wa q o' ≠ wa ptr o)
    (hD1 : ∀ q ∈ Tb, q ≠ ptr → ∀ o o' : U64, o.val < 4096 → o.val % 8 = 0 → o'.val < 4096 → o'.val % 8 = 0 →
      wa q o' ≠ wa ptr o) :
    vspace.decode_page_table st ar s a fl4_abi.label.ARMPageTableUnmap len slot
      (.PageTable ptr true masid mvaddr) buf extra ⦃ r => r.2.1 = s ∨
        (L.ksb r.2.1 = kb ∧ VsTyR st kb Pp Hr Tb Lv r.2.1 ∧ S2TyR st hPl.ipa Pp Hr Te Re bits r.2.1 ∧
          UnmZ st OS Pt (S2Rt st Pp Te Re bits r.2.1) bits r.2.1 ∧ UnmT st OS (VsRt st Pp Hr Tb Lv r.2.1) r.2.1 ∧
          UnmU st OS Pp r.2.1) ⦄ :=
  vspace.decode_page_table.unmapRF hA hPl hR hO q hk hPp hTb hTe hH hS hY h2 hU hT hV hM hRO hK hO.nz a len slot
    buf extra hsl hc hF hptr hal hfit hD2 hD1

end dec

section mdb
variable {OS : Set U64} {G : List (List U64)}

/-- `cdt.empty_slot.mdbN` with `h0` from `OSOK`. -/
theorem cdt.empty_slot.mdbO {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS) {s : S}
    (hM : MdbLk st OS G s) (hRO : RngOneA64 st G s) (hK : KindA st OS s) (hN : NullLk st OS s)
    (hC : ClsA st OS s) {a : A} {x : U64} (hx : x ∈ OS)
    {cl : capability.Cap} {Pw : U64 → Prop} (hpw : ∀ b, Pw b → ¬ InOS OS b)
    (hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
      objects.post_cap_deletion st ar s1 a1 cl ⦃ r => WritesIn st s1 r.1 Pw ⦄) :
    cdt.empty_slot st ar s a x cl ⦃ r => ∃ G' : List (List U64), MdbLk st OS G' r.1 ∧ RngOneA64 st G' r.1 ∧
      KindA st OS r.1 ∧ NullLk st OS r.1 ∧ ClsA st OS r.1 ⦄ :=
  cdt.empty_slot.mdbN hO hO.nz hM hRO hK hN hC hx hpw hpcd

/-- `cdt.cap_swap_for_delete.mdbN` with `h0` from `OSOK`. -/
theorem cdt.cap_swap_for_delete.mdbO (hO : OSOK T Ω Sg OS) {s : S}
    (hM : MdbLk st OS G s) (hRO : RngOneA64 st G s) (hK : KindA st OS s) (hN : NullLk st OS s)
    (hC : ClsA st OS s) {x1 x2 : U64} (hx1 : x1 ∈ OS) (hx2 : x2 ∈ G.flatten) (hs1 : obj.sext48 x1 = ok x1)
    (hs2 : obj.sext48 x2 = ok x2) :
    cdt.cap_swap_for_delete st s x1 x2 ⦃ s' => ∃ G' : List (List U64), MdbLk st OS G' s' ∧ RngOneA64 st G' s' ∧
      KindA st OS s' ∧ NullLk st OS s' ∧ ClsA st OS s' ⦄ :=
  cdt.cap_swap_for_delete.mdbN hO hO.nz hM hRO hK hN hC hx1 hx2 hs1 hs2

/-- `cdt.insert_with_cap.mdbN` with `h0` from `OSOK`. -/
theorem cdt.insert_with_cap.mdbO (hO : OSOK T Ω Sg OS) {s : S}
    (hM : MdbLk st OS G s) (hRO : RngOneA64 st G s) (hK : KindA st OS s) (hN : NullLk st OS s)
    (hC : ClsA st OS s) {src dest : U64} {nc sc : capability.Cap}
    (hsrc : src ∈ G.flatten) (hd : dest ∈ OS) (hd0 : capA st s dest = .Null) (hdc : obj.sext48 dest = ok dest)
    (hsc : capA st s src = sc) (hw : CapRt.EncWf nc) (hnc : nc ≠ .Null) (hA : AlikeA nc sc) :
    cdt.insert_with_cap st s nc sc src dest ⦃ s' => MdbLk st OS (insG src dest G) s' ∧
      RngOneA64 st (insG src dest G) s' ∧ KindA st OS s' ∧ NullLk st OS s' ∧ ClsA st OS s' ⦄ :=
  cdt.insert_with_cap.mdbN hO hO.nz hM hRO hK hN hC hsrc hd hd0 hdc hsc hw hnc hA

/-- `cdt.insert.mdbN` with `h0` from `OSOK`. -/
theorem cdt.insert.mdbO (hO : OSOK T Ω Sg OS) {s : S} (hM : MdbLk st OS G s)
    (hRO : RngOneA64 st G s) (hK : KindA st OS s) (hN : NullLk st OS s) (hC : ClsA st OS s) {src dest : U64}
    {nc : capability.Cap} (hsrc : src ∈ G.flatten) (hd : dest ∈ OS) (hd0 : capA st s dest = .Null)
    (hdc : obj.sext48 dest = ok dest) (hw : CapRt.EncWf nc) (hnc : nc ≠ .Null) (hA : AlikeA nc (capA st s src)) :
    cdt.insert st s nc src dest ⦃ s' => MdbLk st OS (insG src dest G) s' ∧
      RngOneA64 st (insG src dest G) s' ∧ KindA st OS s' ∧ NullLk st OS s' ∧ ClsA st OS s' ⦄ :=
  cdt.insert.mdbN hO hO.nz hM hRO hK hN hC hsrc hd hd0 hdc hw hnc hA

end mdb

end ST
end R
end W7

end

end Fl4ProofsA64.P1
