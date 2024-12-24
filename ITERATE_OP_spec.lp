require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6013661 [_122572 _122573] : Prf (∀ (λ op : El (fun _122573 (fun _122573 _122573)), (⇒ ((@monoidal _122573) op) (∀ (λ f : El (fun _122572 _122573), (∀ (λ g : El (fun _122572 _122573), (∀ (λ s : El (fun _122572 bool), (⇒ ((@FINITE _122572) s) (= ((@iterate _122573 _122572) op s (λ x : El _122572, (op (f x) (g x)))) (op ((@iterate _122573 _122572) op s f) ((@iterate _122573 _122572) op s g)))))))))))));
