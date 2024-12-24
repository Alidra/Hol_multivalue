require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3184729 [_83123] : Prf (∀ (λ P : El (fun (fun bool (fun _83123 bool)) bool), (∀ (λ x : El _83123, (= ((@GSPEC _83123) (λ v : El _83123, (P ((@SETSPEC _83123) v))) x) (P (λ p : El bool, (λ t : El _83123, (∧ p (= x t))))))))));
