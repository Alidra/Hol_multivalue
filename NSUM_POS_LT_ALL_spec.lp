require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6960118 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ f : El (fun A num), (⇒ (∧ ((@FINITE A) s) (∧ (¬ (= s (@EMPTY A))) (∀ (λ i : El A, (⇒ ((@IN A) i s) (< (NUMERAL _0) (f i))))))) (< (NUMERAL _0) ((@nsum A) s f)))))));
