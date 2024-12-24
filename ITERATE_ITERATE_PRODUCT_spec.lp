require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5970042 [A B C] : Prf (∀ (λ op : El (fun C (fun C C)), (⇒ ((@monoidal C) op) (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A (fun B bool)), (∀ (λ x : El (fun A (fun B C)), (⇒ (∧ ((@FINITE A) s) (∀ (λ i : El A, (⇒ ((@IN A) i s) ((@FINITE B) (t i)))))) (= ((@iterate C A) op s (λ i : El A, ((@iterate C B) op (t i) (x i)))) ((@iterate C (prod A B)) op ((@GSPEC (prod A B)) (λ GEN_PVAR_241 : El (prod A B), (∃ (λ i : El A, (∃ (λ j : El B, ((@SETSPEC (prod A B)) GEN_PVAR_241 (∧ ((@IN A) i s) ((@IN B) j (t i))) ((@̦‚ A B) i j)))))))) ((@GABS (fun (prod A B) C)) (λ f : El (fun (prod A B) C), (∀ (λ i : El A, (∀ (λ j : El B, ((@GEQ C) (f ((@̦‚ A B) i j)) (x i j))))))))))))))))))));
