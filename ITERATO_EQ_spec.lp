require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6861305 [A K] : Prf (∀ (λ dom : El (fun A bool), (∀ (λ neut : El A, (∀ (λ op : El (fun A (fun A A)), (∀ (λ <<= : El (fun K (fun K bool)), (∀ (λ k : El (fun K bool), (∀ (λ f : El (fun K A), (∀ (λ g : El (fun K A), (⇒ (∀ (λ i : El K, (⇒ ((@IN K) i k) (= (f i) (g i))))) (= ((@iterato A K) dom neut op <<= k f) ((@iterato A K) dom neut op <<= k g)))))))))))))))));
