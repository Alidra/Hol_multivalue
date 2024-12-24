require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7081142 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ f : El (fun A real), (⇒ (∧ ((@FINITE A) s) (∧ (¬ (= s (@EMPTY A))) (∀ (λ i : El A, (⇒ ((@IN A) i s) (real_lt (real_of_num (NUMERAL _0)) (f i))))))) (real_lt (real_of_num (NUMERAL _0)) ((@sum A) s f)))))));
