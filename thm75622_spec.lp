require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem75622 (P : El (fun num bool)) : Prf ((λ P' : El (fun num bool), (⇒ (∧ (P' (NUMERAL _0)) (∀ (λ n : El num, (⇒ (P' n) (P' (SUC n)))))) (∀ (λ n : El num, (P' n))))) P);
