require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7188776 [A] : Prf (∀ (λ f : El (fun A real), (∀ (λ s : El (fun (fun A bool) bool), (⇒ (∧ ((@FINITE (fun A bool)) s) (∧ (∀ (λ t : El (fun A bool), (⇒ ((@IN (fun A bool)) t s) ((@FINITE A) t)))) (∀ (λ t1 : El (fun A bool), (∀ (λ t2 : El (fun A bool), (∀ (λ x : El A, (⇒ (∧ ((@IN (fun A bool)) t1 s) (∧ ((@IN (fun A bool)) t2 s) (∧ (¬ (= t1 t2)) (∧ ((@IN A) x t1) ((@IN A) x t2))))) (= (f x) (real_of_num (NUMERAL _0)))))))))))) (= ((@sum A) ((@UNIONS A) s) f) ((@sum (fun A bool)) s (λ t : El (fun A bool), ((@sum A) t f)))))))));
