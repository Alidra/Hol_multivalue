require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7068426 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (∀ (λ f : El (fun A real), (⇒ (∧ ((@FINITE A) s) ((@FINITE A) t)) (= (real_add ((@sum A) s f) ((@sum A) t f)) (real_add ((@sum A) ((@UNION A) s t) f) ((@sum A) ((@INTER A) s t) f))))))))));
