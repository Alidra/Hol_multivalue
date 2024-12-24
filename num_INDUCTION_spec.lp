require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem75586 : Prf (∀ (λ P : El (fun num bool), (⇒ (∧ (P (NUMERAL _0)) (∀ (λ n : El num, (⇒ (P n) (P (SUC n)))))) (∀ (λ n : El num, (P n))))));
