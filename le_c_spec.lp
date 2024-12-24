require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5120869 [_114929 _114934] : Prf (∀ (λ t : El (fun _114929 bool), (∀ (λ s : El (fun _114934 bool), (= ((@<=_c _114929 _114934) s t) (∃ (λ f : El (fun _114934 _114929), (∧ (∀ (λ x : El _114934, (⇒ ((@IN _114934) x s) ((@IN _114929) (f x) t)))) (∀ (λ x : El _114934, (∀ (λ y : El _114934, (⇒ (∧ ((@IN _114934) x s) (∧ ((@IN _114934) y s) (= (f x) (f y)))) (= x y))))))))))))));
