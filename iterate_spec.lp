require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5718049 [_119779 A] : Prf (∀ (λ f : El (fun A _119779), (∀ (λ s : El (fun A bool), (∀ (λ op : El (fun _119779 (fun _119779 _119779)), (= ((@iterate _119779 A) op s f) ((@COND _119779) ((@FINITE A) ((@support A _119779) op f s)) ((@ITSET _119779 A) (λ x : El A, (λ a : El _119779, (op (f x) a))) ((@support A _119779) op f s) ((@neutral _119779) op)) ((@neutral _119779) op)))))))));
