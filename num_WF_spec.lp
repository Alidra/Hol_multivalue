require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem115780 : Prf (∀ (λ P : El (fun num bool), (⇒ (∀ (λ n : El num, (⇒ (∀ (λ m : El num, (⇒ (< m n) (P m)))) (P n)))) (∀ (λ n : El num, (P n))))));
