require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem254652 (a : El num) (b : El num) (P : El (fun num bool)) : Prf (= (P (- a b)) (∀ (λ d : El num, (⇒ (∨ (= a (+ b d)) (∧ (< a b) (= d (NUMERAL _0)))) (P d)))));
