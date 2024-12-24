require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3862701 [A] : Prf (∀ (λ P : El (fun (fun A bool) bool), (⇒ (∧ (P (@EMPTY A)) (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (¬ (= s (@EMPTY A)))) (∃ (λ x : El A, (∧ ((@IN A) x s) (⇒ (P ((@DELETE A) s x)) (P s))))))))) (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) s) (P s)))))));
