require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem75635 [A] : Prf (∀ (λ e : El A, (∀ (λ f : El (fun A (fun num A)), (∃ (λ fn : El (fun num A), (∧ (= (fn (NUMERAL _0)) e) (∀ (λ n : El num, (= (fn (SUC n)) (f (fn n) n)))))))))));
