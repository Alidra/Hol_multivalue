require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6875679 [A K] : Prf (∀ (λ dom : El (fun A bool), (∀ (λ neut : El A, (∀ (λ op : El (fun A (fun A A)), (∀ (λ <<= : El (fun K (fun K bool)), (∀ (λ k : El (fun K bool), (∀ (λ f : El (fun K A), (∀ (λ P : El (fun A bool), (⇒ (∧ (P neut) (∧ (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ (P x) (P y)) (P (op x y))))))) (∀ (λ i : El K, (⇒ (∧ ((@IN K) i k) (∧ ((@IN A) (f i) dom) (¬ (= (f i) neut)))) (P (f i))))))) (P ((@iterato A K) dom neut op <<= k f)))))))))))))))));
