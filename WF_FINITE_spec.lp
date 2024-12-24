require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5113408 [A] : Prf (∀ (λ << : El (fun A (fun A bool)), (⇒ (∧ (∀ (λ x : El A, (¬ (<< x x)))) (∧ (∀ (λ x : El A, (∀ (λ y : El A, (∀ (λ z : El A, (⇒ (∧ (<< x y) (<< y z)) (<< x z)))))))) (∀ (λ x : El A, ((@FINITE A) ((@GSPEC A) (λ GEN_PVAR_227 : El A, (∃ (λ y : El A, ((@SETSPEC A) GEN_PVAR_227 (<< y x) y)))))))))) ((@WF A) <<))));
