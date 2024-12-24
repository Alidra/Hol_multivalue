require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8093231 [_143449 _143452 _143456 _143457 _143462] : Prf (∀ (λ p : El (fun (fun _143456 _143452) (fun _143462 bool)), (∀ (λ << : El (fun _143456 (fun _143449 bool)), (∀ (λ s : El (fun _143462 _143449), (∀ (λ t : El (fun (fun _143456 _143452) (fun _143462 _143457)), (= ((@admissible _143449 _143452 _143456 _143457 _143462) << p s t) (∀ (λ f : El (fun _143456 _143452), (∀ (λ g : El (fun _143456 _143452), (∀ (λ a : El _143462, (⇒ (∧ (p f a) (∧ (p g a) (∀ (λ z : El _143456, (⇒ (<< z (s a)) (= (f z) (g z))))))) (= (t f a) (t g a))))))))))))))))));
