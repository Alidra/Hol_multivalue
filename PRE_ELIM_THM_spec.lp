require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem247261 (n : El num) (P : El (fun num bool)) : Prf (= (P (PRE n)) (∀ (λ m : El num, (⇒ (∨ (= n (SUC m)) (∧ (= m (NUMERAL _0)) (= n (NUMERAL _0)))) (P m)))));
