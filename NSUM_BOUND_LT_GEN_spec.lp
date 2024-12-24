require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6982957 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ f : El (fun A num), (∀ (λ b : El num, (⇒ (∧ ((@FINITE A) s) (∧ (¬ (= s (@EMPTY A))) (∀ (λ x : El A, (⇒ ((@IN A) x s) (< (f x) (DIV b ((@CARD A) s)))))))) (< ((@nsum A) s f) b))))))));
