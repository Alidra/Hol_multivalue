require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7178267 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A (fun B bool)), (∀ (λ x : El (fun A (fun B real)), (⇒ (∧ ((@FINITE A) s) (∀ (λ i : El A, (⇒ ((@IN A) i s) ((@FINITE B) (t i)))))) (= ((@sum A) s (λ i : El A, ((@sum B) (t i) (x i)))) ((@sum (prod A B)) ((@GSPEC (prod A B)) (λ GEN_PVAR_327 : El (prod A B), (∃ (λ i : El A, (∃ (λ j : El B, ((@SETSPEC (prod A B)) GEN_PVAR_327 (∧ ((@IN A) i s) ((@IN B) j (t i))) ((@̦‚ A B) i j)))))))) ((@GABS (fun (prod A B) real)) (λ f : El (fun (prod A B) real), (∀ (λ i : El A, (∀ (λ j : El B, ((@GEQ real) (f ((@̦‚ A B) i j)) (x i j)))))))))))))))));
