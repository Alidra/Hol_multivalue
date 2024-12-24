require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7017695 [A] : Prf (∀ (λ a : El (fun A num), (∀ (λ b : El (fun A num), (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) s) (<= ((@nsum A) s (λ i : El A, (* (a i) (b i)))) (* ((@nsum A) s a) ((@nsum A) s b))))))))));
