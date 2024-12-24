require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4067919 [_102240 _102247] : Prf (∀ (λ P : El (fun (fun _102247 bool) bool), (∀ (λ f : El (fun _102240 _102247), (∀ (λ s : El (fun _102240 bool), (∀ (λ n : El num, (= (∀ (λ t : El (fun _102247 bool), (⇒ (∧ ((@FINITE _102247) t) (∧ (< ((@CARD _102247) t) n) ((@SUBSET _102247) t ((@IMAGE _102240 _102247) f s)))) (P t)))) (∀ (λ t : El (fun _102240 bool), (⇒ (∧ ((@FINITE _102240) t) (∧ (< ((@CARD _102240) t) n) (∧ ((@SUBSET _102240) t s) (∀ (λ x : El _102240, (∀ (λ y : El _102240, (⇒ (∧ ((@IN _102240) x t) ((@IN _102240) y t)) (= (= (f x) (f y)) (= x y)))))))))) (P ((@IMAGE _102240 _102247) f t))))))))))))));
