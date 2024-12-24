Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PAIRWISE_INSERT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import IN_INSERT_spec.
Require Import pairwise_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Lemma lem4802031 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4802032 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4802033 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4802032 t1) (@lem4802031 t1)). Qed.
Lemma lem4802034 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4802033 t1 t2). Qed.
Lemma lem4802035 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4802036 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4802035 t1 t2) (@lem4802034 t1 t2)). Qed.
Lemma lem4802037 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4802036 t1 t2 t3). Qed.
Lemma lem4802038 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4802039 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4802038 t1 t2 t3) (@lem4802037 t1 t2 t3)). Qed.
Lemma lem4802040 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4802039 t1 t2 t3)). Qed.
Lemma lem4802041 {A : Type'} (x : A) : term7 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem4802042 {A : Type'} (x : A) : (term7 A x) = (term8 A x).
Proof. exact (eq_refl (term7 A x)). Qed.
Lemma lem4802043 {A : Type'} (x : A) : term8 A x.
Proof. exact (EQ_MP (@lem4802042 A x) (@lem4802041 A x)). Qed.
Lemma lem4802044 {A : Type'} (x : A) (y : A) : term9 A x y.
Proof. exact (@lem4802043 A x y). Qed.
Lemma lem4802045 {A : Type'} (y : A) (x : A) : (term9 A x y) = (term10 A y x).
Proof. exact (eq_refl (term9 A x y)). Qed.
Lemma lem4802046 {A : Type'} (y : A) (x : A) : term10 A y x.
Proof. exact (EQ_MP (@lem4802045 A y x) (@lem4802044 A x y)). Qed.
Lemma lem4802047 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term11 A y x s.
Proof. exact (@lem4802046 A y x s). Qed.
Lemma lem4802048 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term11 A y x s) = ((term12 A x y s) = (term13 A y x s)).
Proof. exact (eq_refl (term11 A y x s)). Qed.
Lemma lem4802050 {_110510 : Type'} (s : _110510 -> Prop) : term14 _110510 s.
Proof. exact (@lem4794393 _110510 s). Qed.
Lemma lem4802051 {_110510 : Type'} (s : _110510 -> Prop) : (term14 _110510 s) = (term15 _110510 s).
Proof. exact (eq_refl (term14 _110510 s)). Qed.
Lemma lem4802052 {_110510 : Type'} (s : _110510 -> Prop) : term15 _110510 s.
Proof. exact (EQ_MP (@lem4802051 _110510 s) (@lem4802050 _110510 s)). Qed.
Lemma lem4802053 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : term16 _110510 s r.
Proof. exact (@lem4802052 _110510 s r). Qed.
Lemma lem4802054 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (term16 _110510 s r) = ((@pairwise _110510 r s) = (term17 _110510 s r)).
Proof. exact (eq_refl (term16 _110510 s r)). Qed.
Lemma lem4802071 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (@pairwise _110510 r s) = (term17 _110510 s r).
Proof. exact (EQ_MP (@lem4802054 _110510 s r) (@lem4802053 _110510 s r)). Qed.
Lemma lem4802072 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) : (@pairwise _110698 r s) = (term17 _110698 s r).
Proof. exact (@lem4802071 _110698 s r). Qed.
Lemma lem4802073 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term18 _110698 r x s) = (term19 _110698 x s r).
Proof. exact (@lem4802072 _110698 (@INSERT _110698 x s) r). Qed.
Lemma lem4802087 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term12 A x y s) = (term13 A y x s).
Proof. exact (EQ_MP (@lem4802048 A y x s) (@lem4802047 A y x s)). Qed.
Lemma lem4802088 {_110698 : Type'} (y : _110698) (x : _110698) (s : _110698 -> Prop) : (term12 _110698 x y s) = (term13 _110698 y x s).
Proof. exact (@lem4802087 _110698 y x s). Qed.
Lemma lem4802089 {_110698 : Type'} (x : _110698) (x' : _110698) (s : _110698 -> Prop) : (term12 _110698 x' x s) = (term13 _110698 x x' s).
Proof. exact (@lem4802088 _110698 x x' s). Qed.
Lemma lem4802094 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4802095 {_110698 : Type'} (x : _110698) (x' : _110698) (s : _110698 -> Prop) : (term20 _110698 x' x s) = (term21 _110698 x x' s).
Proof. exact (MK_COMB (@lem4802094) (@lem4802089 _110698 x x' s)). Qed.
Lemma lem4802099 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term12 A x y s) = (term13 A y x s).
Proof. exact (EQ_MP (@lem4802048 A y x s) (@lem4802047 A y x s)). Qed.
Lemma lem4802100 {_110698 : Type'} (y : _110698) (x : _110698) (s : _110698 -> Prop) : (term12 _110698 x y s) = (term13 _110698 y x s).
Proof. exact (@lem4802099 _110698 y x s). Qed.
Lemma lem4802101 {_110698 : Type'} (x : _110698) (y : _110698) (s : _110698 -> Prop) : (term12 _110698 y x s) = (term13 _110698 x y s).
Proof. exact (@lem4802100 _110698 x y s). Qed.
Lemma lem4802106 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4802107 {_110698 : Type'} (x : _110698) (y : _110698) (s : _110698 -> Prop) : (term20 _110698 y x s) = (term21 _110698 x y s).
Proof. exact (MK_COMB (@lem4802106) (@lem4802101 _110698 x y s)). Qed.
Lemma lem4802110 {_110698 : Type'} (x' : _110698) (y : _110698) : (term22 _110698 x' y) = (term22 _110698 x' y).
Proof. exact (eq_refl (term22 _110698 x' y)). Qed.
Lemma lem4802111 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term23 _110698 x s x' y) = (term24 _110698 x s x' y).
Proof. exact (MK_COMB (@lem4802107 _110698 x y s) (@lem4802110 _110698 x' y)). Qed.
Lemma lem4802114 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term25 _110698 x s x' y) = (term26 _110698 x s x' y).
Proof. exact (MK_COMB (@lem4802095 _110698 x x' s) (@lem4802111 _110698 x s x' y)). Qed.
Lemma lem4802117 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4802118 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term27 _110698 x s x' y) = (term28 _110698 x s x' y).
Proof. exact (MK_COMB (@lem4802117) (@lem4802114 _110698 x s x' y)). Qed.
Lemma lem4802119 {_110698 : Type'} (r : type1402 _110698) (x' : _110698) (y : _110698) : (r x' y) = (r x' y).
Proof. exact (eq_refl (r x' y)). Qed.
Lemma lem4802120 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term29 _110698 x s r x' y) = (term30 _110698 x s r x' y).
Proof. exact (MK_COMB (@lem4802118 _110698 x s x' y) (@lem4802119 _110698 r x' y)). Qed.
Lemma lem4802123 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term31 _110698 x s r x') = (term32 _110698 x s r x').
Proof. exact (fun_ext (fun y : _110698 => @lem4802120 _110698 x s r x' y)). Qed.
Lemma lem4802124 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4802125 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term33 _110698 x s r x') = (term34 _110698 x s r x').
Proof. exact (MK_COMB (@lem4802124 _110698) (@lem4802123 _110698 x s r x')). Qed.
Lemma lem4802130 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term35 _110698 x s r) = (term36 _110698 x s r).
Proof. exact (fun_ext (fun x' : _110698 => @lem4802125 _110698 x s r x')). Qed.
Lemma lem4802131 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4802132 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term19 _110698 x s r) = (term37 _110698 x s r).
Proof. exact (MK_COMB (@lem4802131 _110698) (@lem4802130 _110698 x s r)). Qed.
Lemma lem4802137 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term18 _110698 r x s) = (term37 _110698 x s r).
Proof. exact (TRANS (@lem4802073 _110698 x s r) (@lem4802132 _110698 x s r)). Qed.
Lemma lem4802138 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4802139 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term38 _110698 r x s) = (term39 _110698 x s r).
Proof. exact (MK_COMB (@lem4802138) (@lem4802137 _110698 x s r)). Qed.
Lemma lem4802155 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (@pairwise _110510 r s) = (term17 _110510 s r).
Proof. exact (EQ_MP (@lem4802054 _110510 s r) (@lem4802053 _110510 s r)). Qed.
Lemma lem4802156 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) : (@pairwise _110698 r s) = (term17 _110698 s r).
Proof. exact (@lem4802155 _110698 s r). Qed.
Lemma lem4802173 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term40 _110698 s r x) = (term40 _110698 s r x).
Proof. exact (eq_refl (term40 _110698 s r x)). Qed.
Lemma lem4802174 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term41 _110698 x r s) = (term42 _110698 x s r).
Proof. exact (MK_COMB (@lem4802173 _110698 s r x) (@lem4802156 _110698 s r)). Qed.
Lemma lem4802177 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : ((term18 _110698 r x s) = (term41 _110698 x r s)) = ((term37 _110698 x s r) = (term42 _110698 x s r)).
Proof. exact (MK_COMB (@lem4802139 _110698 x s r) (@lem4802174 _110698 x s r)). Qed.
Lemma lem4802180 {_110698 : Type'} (x : _110698) (r : type1402 _110698) : (term43 _110698 x r) = (term44 _110698 x r).
Proof. exact (fun_ext (fun s : _110698 -> Prop => @lem4802177 _110698 x s r)). Qed.
Lemma lem4802181 {_110698 : Type'} : (@all (_110698 -> Prop)) = (@all (_110698 -> Prop)).
Proof. exact (eq_refl (@all (_110698 -> Prop))). Qed.
Lemma lem4802182 {_110698 : Type'} (x : _110698) (r : type1402 _110698) : (term45 _110698 x r) = (term46 _110698 x r).
Proof. exact (MK_COMB (@lem4802181 _110698) (@lem4802180 _110698 x r)). Qed.
Lemma lem4802187 {_110698 : Type'} (r : type1402 _110698) : (term47 _110698 r) = (term48 _110698 r).
Proof. exact (fun_ext (fun x : _110698 => @lem4802182 _110698 x r)). Qed.
Lemma lem4802188 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4802189 {_110698 : Type'} (r : type1402 _110698) : (term49 _110698 r) = (term50 _110698 r).
Proof. exact (MK_COMB (@lem4802188 _110698) (@lem4802187 _110698 r)). Qed.
Lemma lem4802194 {_110698 : Type'} : (term51 _110698) = (term52 _110698).
Proof. exact (fun_ext (fun r : type1402 _110698 => @lem4802189 _110698 r)). Qed.
Lemma lem4802195 {_110698 : Type'} : (@all (_110698 -> _110698 -> Prop)) = (@all (_110698 -> _110698 -> Prop)).
Proof. exact (eq_refl (@all (_110698 -> _110698 -> Prop))). Qed.
Lemma lem4802196 {_110698 : Type'} : (term53 _110698) = (term54 _110698).
Proof. exact (MK_COMB (@lem4802195 _110698) (@lem4802194 _110698)). Qed.
Lemma lem4802201 {_110698 : Type'} : (term54 _110698) = (term53 _110698).
Proof. exact (SYM (@lem4802196 _110698)). Qed.
Lemma lem4802203 (p : Prop) : p = (term55 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4802204 {_110698 : Type'} : (term54 _110698) = (term56 _110698).
Proof. exact (@lem4802203 (term54 _110698)). Qed.
Lemma lem4802205 {_110698 : Type'} : (term56 _110698) = (term54 _110698).
Proof. exact (SYM (@lem4802204 _110698)). Qed.
Lemma lem4802206 {_110698 : Type'} (h1 : term57 _110698) : term57 _110698.
Proof. exact (h1). Qed.
Lemma lem4802209 {_110698 : Type'} (h1 : term56 _110698) : term56 _110698.
Proof. exact (h1). Qed.
Lemma lem4802210 {_110698 : Type'} : term58 _110698.
Proof. exact (fun h0 : term56 _110698 => @lem4802209 _110698 h0). Qed.
Lemma lem4802211 {_110698 : Type'} (h1 : term58 _110698) : term58 _110698.
Proof. exact (h1). Qed.
Lemma lem4802212 {_110698 : Type'} (h1 : term56 _110698) : term56 _110698.
Proof. exact (h1). Qed.
Lemma lem4802213 {_110698 : Type'} (h1 : term56 _110698) (h2 : term58 _110698) : term56 _110698.
Proof. exact (@lem4802211 _110698 h2 (@lem4802212 _110698 h1)). Qed.
Lemma lem4802214 {_110698 : Type'} (h1 : term56 _110698) : term59 _110698.
Proof. exact (fun h0 : term58 _110698 => @lem4802213 _110698 h1 h0). Qed.
Lemma lem4802215 {_110698 : Type'} (h1 : term58 _110698) : term58 _110698.
Proof. exact (h1). Qed.
Lemma lem4802216 {_110698 : Type'} (h1 : term56 _110698) (h2 : term58 _110698) : term56 _110698.
Proof. exact (@lem4802214 _110698 h1 (@lem4802215 _110698 h2)). Qed.
Lemma lem4802217 {_110698 : Type'} (h1 : term58 _110698) : term58 _110698.
Proof. exact (fun h0 : term56 _110698 => @lem4802216 _110698 h0 h1). Qed.
Lemma lem4802218 {_110698 : Type'} : term60 _110698.
Proof. exact (fun h0 : term58 _110698 => @lem4802217 _110698 h0). Qed.
Lemma lem4802221 {_110698 : Type'} : term58 _110698.
Proof. exact (@lem4802218 _110698 (@lem4802210 _110698)). Qed.
Lemma lem4802222 {_110698 : Type'} : term58 _110698.
Proof. exact (@lem4802221 _110698). Qed.
Lemma lem4802224 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4802225 {_110698 : Type'} : (term56 _110698) = (term61 _110698).
Proof. exact (@lem4802224 (term57 _110698)). Qed.
Lemma lem4802227 (t : Prop) : (term62 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4802228 {_110698 : Type'} : (term61 _110698) = (term54 _110698).
Proof. exact (@lem4802227 (term54 _110698)). Qed.
Lemma lem4802289 {_110698 : Type'} : (term56 _110698) = (term54 _110698).
Proof. exact (TRANS (@lem4802225 _110698) (@lem4802228 _110698)). Qed.
Lemma lem4802304 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) (y : _110698) : (term63 _110698 s r x y) = (term63 _110698 s r x y).
Proof. exact (eq_refl (term63 _110698 s r x y)). Qed.
Lemma lem4802305 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term64 _110698 s r x) = (term64 _110698 s r x).
Proof. exact (fun_ext (fun y : _110698 => @lem4802304 _110698 s r x y)). Qed.
Lemma lem4802306 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4802307 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term65 _110698 s r x) = (term65 _110698 s r x).
Proof. exact (MK_COMB (@lem4802306 _110698) (@lem4802305 _110698 s r x)). Qed.
Lemma lem4802308 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) : (term66 _110698 s r) = (term66 _110698 s r).
Proof. exact (fun_ext (fun x : _110698 => @lem4802307 _110698 s r x)). Qed.
Lemma lem4802309 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4802310 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) : (term17 _110698 s r) = (term17 _110698 s r).
Proof. exact (MK_COMB (@lem4802309 _110698) (@lem4802308 _110698 s r)). Qed.
Lemma lem4802325 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) : (term67 _110698 s r y x) = (term67 _110698 s r y x).
Proof. exact (eq_refl (term67 _110698 s r y x)). Qed.
Lemma lem4802326 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term68 _110698 s r x) = (term68 _110698 s r x).
Proof. exact (fun_ext (fun y : _110698 => @lem4802325 _110698 s r y x)). Qed.
Lemma lem4802327 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4802328 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term69 _110698 s r x) = (term69 _110698 s r x).
Proof. exact (MK_COMB (@lem4802327 _110698) (@lem4802326 _110698 s r x)). Qed.
Lemma lem4802329 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4802330 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term40 _110698 s r x) = (term40 _110698 s r x).
Proof. exact (MK_COMB (@lem4802329) (@lem4802328 _110698 s r x)). Qed.
Lemma lem4802331 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term42 _110698 x s r) = (term42 _110698 x s r).
Proof. exact (MK_COMB (@lem4802330 _110698 s r x) (@lem4802310 _110698 s r)). Qed.
Lemma lem4802354 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term30 _110698 x s r x' y) = (term30 _110698 x s r x' y).
Proof. exact (eq_refl (term30 _110698 x s r x' y)). Qed.
Lemma lem4802355 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term32 _110698 x s r x') = (term32 _110698 x s r x').
Proof. exact (fun_ext (fun y : _110698 => @lem4802354 _110698 x s r x' y)). Qed.
Lemma lem4802356 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4802357 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term34 _110698 x s r x') = (term34 _110698 x s r x').
Proof. exact (MK_COMB (@lem4802356 _110698) (@lem4802355 _110698 x s r x')). Qed.
Lemma lem4802358 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term36 _110698 x s r) = (term36 _110698 x s r).
Proof. exact (fun_ext (fun x' : _110698 => @lem4802357 _110698 x s r x')). Qed.
Lemma lem4802359 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4802360 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term37 _110698 x s r) = (term37 _110698 x s r).
Proof. exact (MK_COMB (@lem4802359 _110698) (@lem4802358 _110698 x s r)). Qed.
Lemma lem4802361 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4802362 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term39 _110698 x s r) = (term39 _110698 x s r).
Proof. exact (MK_COMB (@lem4802361) (@lem4802360 _110698 x s r)). Qed.
Lemma lem4802363 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : ((term37 _110698 x s r) = (term42 _110698 x s r)) = ((term37 _110698 x s r) = (term42 _110698 x s r)).
Proof. exact (MK_COMB (@lem4802362 _110698 x s r) (@lem4802331 _110698 x s r)). Qed.
Lemma lem4802364 {_110698 : Type'} (x : _110698) (r : type1402 _110698) : (term44 _110698 x r) = (term44 _110698 x r).
Proof. exact (fun_ext (fun s : _110698 -> Prop => @lem4802363 _110698 x s r)). Qed.
Lemma lem4802365 {_110698 : Type'} : (@all (_110698 -> Prop)) = (@all (_110698 -> Prop)).
Proof. exact (eq_refl (@all (_110698 -> Prop))). Qed.
Lemma lem4802366 {_110698 : Type'} (x : _110698) (r : type1402 _110698) : (term46 _110698 x r) = (term46 _110698 x r).
Proof. exact (MK_COMB (@lem4802365 _110698) (@lem4802364 _110698 x r)). Qed.
Lemma lem4802367 {_110698 : Type'} (r : type1402 _110698) : (term48 _110698 r) = (term48 _110698 r).
Proof. exact (fun_ext (fun x : _110698 => @lem4802366 _110698 x r)). Qed.
Lemma lem4802368 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4802369 {_110698 : Type'} (r : type1402 _110698) : (term50 _110698 r) = (term50 _110698 r).
Proof. exact (MK_COMB (@lem4802368 _110698) (@lem4802367 _110698 r)). Qed.
Lemma lem4802370 {_110698 : Type'} : (term52 _110698) = (term52 _110698).
Proof. exact (fun_ext (fun r : type1402 _110698 => @lem4802369 _110698 r)). Qed.
Lemma lem4802371 {_110698 : Type'} : (@all (_110698 -> _110698 -> Prop)) = (@all (_110698 -> _110698 -> Prop)).
Proof. exact (eq_refl (@all (_110698 -> _110698 -> Prop))). Qed.
Lemma lem4802372 {_110698 : Type'} : (term54 _110698) = (term54 _110698).
Proof. exact (MK_COMB (@lem4802371 _110698) (@lem4802370 _110698)). Qed.
Lemma lem4802447 {_110698 : Type'} : (term56 _110698) = (term54 _110698).
Proof. exact (TRANS (@lem4802289 _110698) (@lem4802372 _110698)). Qed.
Lemma lem4802448 {_110698 : Type'} : (term54 _110698) = (term56 _110698).
Proof. exact (SYM (@lem4802447 _110698)). Qed.
Lemma lem4802450 (p : Prop) : p = (term55 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4802451 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : ((term37 _110698 x s r) = (term42 _110698 x s r)) = (term70 _110698 x s r).
Proof. exact (@lem4802450 ((term37 _110698 x s r) = (term42 _110698 x s r))). Qed.
Lemma lem4802452 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term70 _110698 x s r) = ((term37 _110698 x s r) = (term42 _110698 x s r)).
Proof. exact (SYM (@lem4802451 _110698 x s r)). Qed.
Lemma lem4802453 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term71 _110698 x s r) : term71 _110698 x s r.
Proof. exact (h1). Qed.
Lemma lem4802462 {_110698 : Type'} (x : _110698) (x' : _110698) (s : _110698 -> Prop) : (term72 _110698 x x' s) = (term73 _110698 x x' s).
Proof. exact (@lem17160 (x' = x) (@IN _110698 x' s)). Qed.
Lemma lem4802474 {_110698 : Type'} (x : _110698) (y : _110698) (s : _110698 -> Prop) : (term72 _110698 x y s) = (term73 _110698 x y s).
Proof. exact (@lem17160 (y = x) (@IN _110698 y s)). Qed.
Lemma lem4802481 {_110698 : Type'} (x' : _110698) (y : _110698) : (term74 _110698 x' y) = (x' = y).
Proof. exact (@lem16933 (x' = y)). Qed.
Lemma lem4802482 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4802483 {_110698 : Type'} (x : _110698) (y : _110698) (s : _110698 -> Prop) : (term75 _110698 x y s) = (term76 _110698 x y s).
Proof. exact (MK_COMB (@lem4802482) (@lem4802474 _110698 x y s)). Qed.
Lemma lem4802484 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term77 _110698 x s x' y) = (term78 _110698 x s x' y).
Proof. exact (MK_COMB (@lem4802483 _110698 x y s) (@lem4802481 _110698 x' y)). Qed.
Lemma lem4802485 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term79 _110698 x s x' y) = (term77 _110698 x s x' y).
Proof. exact (@lem17045 (term13 _110698 x y s) (term22 _110698 x' y)). Qed.
Lemma lem4802486 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term79 _110698 x s x' y) = (term78 _110698 x s x' y).
Proof. exact (TRANS (@lem4802485 _110698 x s x' y) (@lem4802484 _110698 x s x' y)). Qed.
Lemma lem4802490 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4802491 {_110698 : Type'} (x : _110698) (x' : _110698) (s : _110698 -> Prop) : (term75 _110698 x x' s) = (term76 _110698 x x' s).
Proof. exact (MK_COMB (@lem4802490) (@lem4802462 _110698 x x' s)). Qed.
Lemma lem4802492 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term80 _110698 x s x' y) = (term81 _110698 x s x' y).
Proof. exact (MK_COMB (@lem4802491 _110698 x x' s) (@lem4802486 _110698 x s x' y)). Qed.
Lemma lem4802493 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term82 _110698 x s x' y) = (term80 _110698 x s x' y).
Proof. exact (@lem17045 (term13 _110698 x x' s) (term24 _110698 x s x' y)). Qed.
Lemma lem4802494 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term82 _110698 x s x' y) = (term81 _110698 x s x' y).
Proof. exact (TRANS (@lem4802493 _110698 x s x' y) (@lem4802492 _110698 x s x' y)). Qed.
Lemma lem4802499 {_110698 : Type'} (r : type1402 _110698) (x' : _110698) (y : _110698) : (r x' y) = (r x' y).
Proof. exact (eq_refl (r x' y)). Qed.
Lemma lem4802504 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term83 _110698 x s r x' y) = (term84 _110698 x s r x' y).
Proof. exact (@lem17362 (term26 _110698 x s x' y) (r x' y)). Qed.
Lemma lem4802505 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4802506 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term85 _110698 x s x' y) = (term86 _110698 x s x' y).
Proof. exact (MK_COMB (@lem4802505) (@lem4802494 _110698 x s x' y)). Qed.
Lemma lem4802507 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term87 _110698 x s r x' y) = (term88 _110698 x s r x' y).
Proof. exact (MK_COMB (@lem4802506 _110698 x s x' y) (@lem4802499 _110698 r x' y)). Qed.
Lemma lem4802508 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term30 _110698 x s r x' y) = (term87 _110698 x s r x' y).
Proof. exact (@lem17265 (term26 _110698 x s x' y) (r x' y)). Qed.
Lemma lem4802509 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term30 _110698 x s r x' y) = (term88 _110698 x s r x' y).
Proof. exact (TRANS (@lem4802508 _110698 x s r x' y) (@lem4802507 _110698 x s r x' y)). Qed.
Lemma lem4802510 {_110698 : Type'} (P : _110698 -> Prop) : (term89 _110698 P) = (term90 _110698 P).
Proof. exact (@lem18392 _110698 P). Qed.
Lemma lem4802511 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term91 _110698 x s r x') = (term92 _110698 x s r x').
Proof. exact (@lem4802510 _110698 (term32 _110698 x s r x')). Qed.
Lemma lem4802512 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term93 _110698 x s r x' y) = (term30 _110698 x s r x' y).
Proof. exact (eq_refl (term93 _110698 x s r x' y)). Qed.
Lemma lem4802513 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4802514 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term94 _110698 x s r x' y) = (term83 _110698 x s r x' y).
Proof. exact (MK_COMB (@lem4802513) (@lem4802512 _110698 x s r x' y)). Qed.
Lemma lem4802515 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term94 _110698 x s r x' y) = (term84 _110698 x s r x' y).
Proof. exact (TRANS (@lem4802514 _110698 x s r x' y) (@lem4802504 _110698 x s r x' y)). Qed.
Lemma lem4802516 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term95 _110698 x s r x') = (term96 _110698 x s r x').
Proof. exact (fun_ext (fun y : _110698 => @lem4802515 _110698 x s r x' y)). Qed.
Lemma lem4802517 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4802518 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term92 _110698 x s r x') = (term97 _110698 x s r x').
Proof. exact (MK_COMB (@lem4802517 _110698) (@lem4802516 _110698 x s r x')). Qed.
Lemma lem4802519 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term91 _110698 x s r x') = (term97 _110698 x s r x').
Proof. exact (TRANS (@lem4802511 _110698 x s r x') (@lem4802518 _110698 x s r x')). Qed.
Lemma lem4802520 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term32 _110698 x s r x') = (term98 _110698 x s r x').
Proof. exact (fun_ext (fun y : _110698 => @lem4802509 _110698 x s r x' y)). Qed.
Lemma lem4802521 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4802522 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term34 _110698 x s r x') = (term99 _110698 x s r x').
Proof. exact (MK_COMB (@lem4802521 _110698) (@lem4802520 _110698 x s r x')). Qed.
Lemma lem4802523 {_110698 : Type'} (P : _110698 -> Prop) : (term89 _110698 P) = (term90 _110698 P).
Proof. exact (@lem18392 _110698 P). Qed.
Lemma lem4802524 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term100 _110698 x s r) = (term101 _110698 x s r).
Proof. exact (@lem4802523 _110698 (term36 _110698 x s r)). Qed.
Lemma lem4802525 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term102 _110698 x s r x') = (term34 _110698 x s r x').
Proof. exact (eq_refl (term102 _110698 x s r x')). Qed.
Lemma lem4802526 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4802527 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term103 _110698 x s r x') = (term91 _110698 x s r x').
Proof. exact (MK_COMB (@lem4802526) (@lem4802525 _110698 x s r x')). Qed.
Lemma lem4802528 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term103 _110698 x s r x') = (term97 _110698 x s r x').
Proof. exact (TRANS (@lem4802527 _110698 x s r x') (@lem4802519 _110698 x s r x')). Qed.
Lemma lem4802529 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term104 _110698 x s r) = (term105 _110698 x s r).
Proof. exact (fun_ext (fun x' : _110698 => @lem4802528 _110698 x s r x')). Qed.
Lemma lem4802530 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4802531 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term101 _110698 x s r) = (term106 _110698 x s r).
Proof. exact (MK_COMB (@lem4802530 _110698) (@lem4802529 _110698 x s r)). Qed.
Lemma lem4802532 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term100 _110698 x s r) = (term106 _110698 x s r).
Proof. exact (TRANS (@lem4802524 _110698 x s r) (@lem4802531 _110698 x s r)). Qed.
Lemma lem4802533 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term36 _110698 x s r) = (term107 _110698 x s r).
Proof. exact (fun_ext (fun x' : _110698 => @lem4802522 _110698 x s r x')). Qed.
Lemma lem4802534 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4802535 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term37 _110698 x s r) = (term108 _110698 x s r).
Proof. exact (MK_COMB (@lem4802534 _110698) (@lem4802533 _110698 x s r)). Qed.
Lemma lem4802541 {_110698 : Type'} (y : _110698) (x : _110698) : (term74 _110698 y x) = (y = x).
Proof. exact (@lem16933 (y = x)). Qed.
Lemma lem4802543 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) : (term109 _110698 y s) = (term109 _110698 y s).
Proof. exact (eq_refl (term109 _110698 y s)). Qed.
Lemma lem4802544 {_110698 : Type'} (s : _110698 -> Prop) (y : _110698) (x : _110698) : (term110 _110698 s y x) = (term111 _110698 s y x).
Proof. exact (MK_COMB (@lem4802543 _110698 y s) (@lem4802541 _110698 y x)). Qed.
Lemma lem4802545 {_110698 : Type'} (s : _110698 -> Prop) (y : _110698) (x : _110698) : (term112 _110698 s y x) = (term110 _110698 s y x).
Proof. exact (@lem17045 (@IN _110698 y s) (term22 _110698 y x)). Qed.
Lemma lem4802546 {_110698 : Type'} (s : _110698 -> Prop) (y : _110698) (x : _110698) : (term112 _110698 s y x) = (term111 _110698 s y x).
Proof. exact (TRANS (@lem4802545 _110698 s y x) (@lem4802544 _110698 s y x)). Qed.
Lemma lem4802558 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) : (term113 _110698 r y x) = (term114 _110698 r y x).
Proof. exact (@lem17045 (r x y) (r y x)). Qed.
Lemma lem4802561 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) : (term115 _110698 r y x) = (term115 _110698 r y x).
Proof. exact (eq_refl (term115 _110698 r y x)). Qed.
Lemma lem4802563 {_110698 : Type'} (s : _110698 -> Prop) (y : _110698) (x : _110698) : (term116 _110698 s y x) = (term116 _110698 s y x).
Proof. exact (eq_refl (term116 _110698 s y x)). Qed.
Lemma lem4802564 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) : (term117 _110698 s r y x) = (term118 _110698 s r y x).
Proof. exact (MK_COMB (@lem4802563 _110698 s y x) (@lem4802558 _110698 r y x)). Qed.
Lemma lem4802565 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) : (term119 _110698 s r y x) = (term117 _110698 s r y x).
Proof. exact (@lem17362 (term120 _110698 s y x) (term115 _110698 r y x)). Qed.
Lemma lem4802566 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) : (term119 _110698 s r y x) = (term118 _110698 s r y x).
Proof. exact (TRANS (@lem4802565 _110698 s r y x) (@lem4802564 _110698 s r y x)). Qed.
Lemma lem4802567 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4802568 {_110698 : Type'} (s : _110698 -> Prop) (y : _110698) (x : _110698) : (term121 _110698 s y x) = (term122 _110698 s y x).
Proof. exact (MK_COMB (@lem4802567) (@lem4802546 _110698 s y x)). Qed.
Lemma lem4802569 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) : (term123 _110698 s r y x) = (term124 _110698 s r y x).
Proof. exact (MK_COMB (@lem4802568 _110698 s y x) (@lem4802561 _110698 r y x)). Qed.
Lemma lem4802570 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) : (term67 _110698 s r y x) = (term123 _110698 s r y x).
Proof. exact (@lem17265 (term120 _110698 s y x) (term115 _110698 r y x)). Qed.
Lemma lem4802571 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) : (term67 _110698 s r y x) = (term124 _110698 s r y x).
Proof. exact (TRANS (@lem4802570 _110698 s r y x) (@lem4802569 _110698 s r y x)). Qed.
Lemma lem4802572 {_110698 : Type'} (P : _110698 -> Prop) : (term89 _110698 P) = (term90 _110698 P).
Proof. exact (@lem18392 _110698 P). Qed.
Lemma lem4802573 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term125 _110698 s r x) = (term126 _110698 s r x).
Proof. exact (@lem4802572 _110698 (term68 _110698 s r x)). Qed.
Lemma lem4802574 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) : (term127 _110698 s r x y) = (term67 _110698 s r y x).
Proof. exact (eq_refl (term127 _110698 s r x y)). Qed.
Lemma lem4802575 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4802576 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) : (term128 _110698 s r x y) = (term119 _110698 s r y x).
Proof. exact (MK_COMB (@lem4802575) (@lem4802574 _110698 s r y x)). Qed.
Lemma lem4802577 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) : (term128 _110698 s r x y) = (term118 _110698 s r y x).
Proof. exact (TRANS (@lem4802576 _110698 s r y x) (@lem4802566 _110698 s r y x)). Qed.
Lemma lem4802578 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term129 _110698 s r x) = (term130 _110698 s r x).
Proof. exact (fun_ext (fun y : _110698 => @lem4802577 _110698 s r y x)). Qed.
Lemma lem4802579 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4802580 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term126 _110698 s r x) = (term131 _110698 s r x).
Proof. exact (MK_COMB (@lem4802579 _110698) (@lem4802578 _110698 s r x)). Qed.
Lemma lem4802581 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term125 _110698 s r x) = (term131 _110698 s r x).
Proof. exact (TRANS (@lem4802573 _110698 s r x) (@lem4802580 _110698 s r x)). Qed.
Lemma lem4802582 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term68 _110698 s r x) = (term132 _110698 s r x).
Proof. exact (fun_ext (fun y : _110698 => @lem4802571 _110698 s r y x)). Qed.
Lemma lem4802583 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4802584 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term69 _110698 s r x) = (term133 _110698 s r x).
Proof. exact (MK_COMB (@lem4802583 _110698) (@lem4802582 _110698 s r x)). Qed.
Lemma lem4802592 {_110698 : Type'} (x : _110698) (y : _110698) : (term74 _110698 x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem4802594 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) : (term109 _110698 y s) = (term109 _110698 y s).
Proof. exact (eq_refl (term109 _110698 y s)). Qed.
Lemma lem4802595 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (y : _110698) : (term134 _110698 s x y) = (term135 _110698 s x y).
Proof. exact (MK_COMB (@lem4802594 _110698 y s) (@lem4802592 _110698 x y)). Qed.
Lemma lem4802596 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (y : _110698) : (term136 _110698 s x y) = (term134 _110698 s x y).
Proof. exact (@lem17045 (@IN _110698 y s) (term22 _110698 x y)). Qed.
Lemma lem4802597 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (y : _110698) : (term136 _110698 s x y) = (term135 _110698 s x y).
Proof. exact (TRANS (@lem4802596 _110698 s x y) (@lem4802595 _110698 s x y)). Qed.
Lemma lem4802602 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) : (term109 _110698 x s) = (term109 _110698 x s).
Proof. exact (eq_refl (term109 _110698 x s)). Qed.
Lemma lem4802603 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (y : _110698) : (term137 _110698 s x y) = (term138 _110698 s x y).
Proof. exact (MK_COMB (@lem4802602 _110698 x s) (@lem4802597 _110698 s x y)). Qed.
Lemma lem4802604 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (y : _110698) : (term139 _110698 s x y) = (term137 _110698 s x y).
Proof. exact (@lem17045 (@IN _110698 x s) (term140 _110698 s x y)). Qed.
Lemma lem4802605 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (y : _110698) : (term139 _110698 s x y) = (term138 _110698 s x y).
Proof. exact (TRANS (@lem4802604 _110698 s x y) (@lem4802603 _110698 s x y)). Qed.
Lemma lem4802610 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (y : _110698) : (r x y) = (r x y).
Proof. exact (eq_refl (r x y)). Qed.
Lemma lem4802615 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) (y : _110698) : (term141 _110698 s r x y) = (term142 _110698 s r x y).
Proof. exact (@lem17362 (term143 _110698 s x y) (r x y)). Qed.
Lemma lem4802616 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4802617 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (y : _110698) : (term144 _110698 s x y) = (term145 _110698 s x y).
Proof. exact (MK_COMB (@lem4802616) (@lem4802605 _110698 s x y)). Qed.
Lemma lem4802618 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) (y : _110698) : (term146 _110698 s r x y) = (term147 _110698 s r x y).
Proof. exact (MK_COMB (@lem4802617 _110698 s x y) (@lem4802610 _110698 r x y)). Qed.
Lemma lem4802619 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) (y : _110698) : (term63 _110698 s r x y) = (term146 _110698 s r x y).
Proof. exact (@lem17265 (term143 _110698 s x y) (r x y)). Qed.
Lemma lem4802620 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) (y : _110698) : (term63 _110698 s r x y) = (term147 _110698 s r x y).
Proof. exact (TRANS (@lem4802619 _110698 s r x y) (@lem4802618 _110698 s r x y)). Qed.
Lemma lem4802621 {_110698 : Type'} (P : _110698 -> Prop) : (term89 _110698 P) = (term90 _110698 P).
Proof. exact (@lem18392 _110698 P). Qed.
Lemma lem4802622 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term148 _110698 s r x) = (term149 _110698 s r x).
Proof. exact (@lem4802621 _110698 (term64 _110698 s r x)). Qed.
Lemma lem4802623 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) (y : _110698) : (term150 _110698 s r x y) = (term63 _110698 s r x y).
Proof. exact (eq_refl (term150 _110698 s r x y)). Qed.
Lemma lem4802624 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4802625 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) (y : _110698) : (term151 _110698 s r x y) = (term141 _110698 s r x y).
Proof. exact (MK_COMB (@lem4802624) (@lem4802623 _110698 s r x y)). Qed.
Lemma lem4802626 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) (y : _110698) : (term151 _110698 s r x y) = (term142 _110698 s r x y).
Proof. exact (TRANS (@lem4802625 _110698 s r x y) (@lem4802615 _110698 s r x y)). Qed.
Lemma lem4802627 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term152 _110698 s r x) = (term153 _110698 s r x).
Proof. exact (fun_ext (fun y : _110698 => @lem4802626 _110698 s r x y)). Qed.
Lemma lem4802628 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4802629 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term149 _110698 s r x) = (term154 _110698 s r x).
Proof. exact (MK_COMB (@lem4802628 _110698) (@lem4802627 _110698 s r x)). Qed.
Lemma lem4802630 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term148 _110698 s r x) = (term154 _110698 s r x).
Proof. exact (TRANS (@lem4802622 _110698 s r x) (@lem4802629 _110698 s r x)). Qed.
Lemma lem4802631 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term64 _110698 s r x) = (term155 _110698 s r x).
Proof. exact (fun_ext (fun y : _110698 => @lem4802620 _110698 s r x y)). Qed.
Lemma lem4802632 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4802633 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term65 _110698 s r x) = (term156 _110698 s r x).
Proof. exact (MK_COMB (@lem4802632 _110698) (@lem4802631 _110698 s r x)). Qed.
Lemma lem4802634 {_110698 : Type'} (P : _110698 -> Prop) : (term89 _110698 P) = (term90 _110698 P).
Proof. exact (@lem18392 _110698 P). Qed.
Lemma lem4802635 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) : (term157 _110698 s r) = (term158 _110698 s r).
Proof. exact (@lem4802634 _110698 (term66 _110698 s r)). Qed.
Lemma lem4802636 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term159 _110698 s r x) = (term65 _110698 s r x).
Proof. exact (eq_refl (term159 _110698 s r x)). Qed.
Lemma lem4802637 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4802638 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term160 _110698 s r x) = (term148 _110698 s r x).
Proof. exact (MK_COMB (@lem4802637) (@lem4802636 _110698 s r x)). Qed.
Lemma lem4802639 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term160 _110698 s r x) = (term154 _110698 s r x).
Proof. exact (TRANS (@lem4802638 _110698 s r x) (@lem4802630 _110698 s r x)). Qed.
Lemma lem4802640 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) : (term161 _110698 s r) = (term162 _110698 s r).
Proof. exact (fun_ext (fun x : _110698 => @lem4802639 _110698 s r x)). Qed.
Lemma lem4802641 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4802642 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) : (term158 _110698 s r) = (term163 _110698 s r).
Proof. exact (MK_COMB (@lem4802641 _110698) (@lem4802640 _110698 s r)). Qed.
Lemma lem4802643 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) : (term157 _110698 s r) = (term163 _110698 s r).
Proof. exact (TRANS (@lem4802635 _110698 s r) (@lem4802642 _110698 s r)). Qed.
Lemma lem4802644 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) : (term66 _110698 s r) = (term164 _110698 s r).
Proof. exact (fun_ext (fun x : _110698 => @lem4802633 _110698 s r x)). Qed.
Lemma lem4802645 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4802646 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) : (term17 _110698 s r) = (term165 _110698 s r).
Proof. exact (MK_COMB (@lem4802645 _110698) (@lem4802644 _110698 s r)). Qed.
Lemma lem4802647 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4802648 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term166 _110698 s r x) = (term167 _110698 s r x).
Proof. exact (MK_COMB (@lem4802647) (@lem4802581 _110698 s r x)). Qed.
Lemma lem4802649 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term168 _110698 x s r) = (term169 _110698 x s r).
Proof. exact (MK_COMB (@lem4802648 _110698 s r x) (@lem4802643 _110698 s r)). Qed.
Lemma lem4802650 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term170 _110698 x s r) = (term168 _110698 x s r).
Proof. exact (@lem17045 (term69 _110698 s r x) (term17 _110698 s r)). Qed.
Lemma lem4802651 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term170 _110698 x s r) = (term169 _110698 x s r).
Proof. exact (TRANS (@lem4802650 _110698 x s r) (@lem4802649 _110698 x s r)). Qed.
Lemma lem4802652 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4802653 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term40 _110698 s r x) = (term171 _110698 s r x).
Proof. exact (MK_COMB (@lem4802652) (@lem4802584 _110698 s r x)). Qed.
Lemma lem4802654 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term42 _110698 x s r) = (term172 _110698 x s r).
Proof. exact (MK_COMB (@lem4802653 _110698 s r x) (@lem4802646 _110698 s r)). Qed.
Lemma lem4802655 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4802656 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term173 _110698 x s r) = (term174 _110698 x s r).
Proof. exact (MK_COMB (@lem4802655) (@lem4802532 _110698 x s r)). Qed.
Lemma lem4802657 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term175 _110698 x s r) = (term176 _110698 x s r).
Proof. exact (MK_COMB (@lem4802656 _110698 x s r) (@lem4802654 _110698 x s r)). Qed.
Lemma lem4802658 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4802659 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term177 _110698 x s r) = (term178 _110698 x s r).
Proof. exact (MK_COMB (@lem4802658) (@lem4802535 _110698 x s r)). Qed.
Lemma lem4802660 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term179 _110698 x s r) = (term180 _110698 x s r).
Proof. exact (MK_COMB (@lem4802659 _110698 x s r) (@lem4802651 _110698 x s r)). Qed.
Lemma lem4802661 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4802662 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term181 _110698 x s r) = (term182 _110698 x s r).
Proof. exact (MK_COMB (@lem4802661) (@lem4802660 _110698 x s r)). Qed.
Lemma lem4802663 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term183 _110698 x s r) = (term184 _110698 x s r).
Proof. exact (MK_COMB (@lem4802662 _110698 x s r) (@lem4802657 _110698 x s r)). Qed.
Lemma lem4802664 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term71 _110698 x s r) = (term183 _110698 x s r).
Proof. exact (@lem17646 (term37 _110698 x s r) (term42 _110698 x s r)). Qed.
Lemma lem4802665 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term71 _110698 x s r) = (term184 _110698 x s r).
Proof. exact (TRANS (@lem4802664 _110698 x s r) (@lem4802663 _110698 x s r)). Qed.
Lemma lem4802972 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term185 A P Q) = (term186 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4802973 {_110698 : Type'} (P : _110698 -> Prop) (Q : _110698 -> Prop) : (term185 _110698 P Q) = (term186 _110698 P Q).
Proof. exact (@lem4802972 _110698 P Q). Qed.
Lemma lem4802974 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term187 _110698 x s r) = (term188 _110698 x s r).
Proof. exact (@lem4802973 _110698 (term130 _110698 s r x) (term162 _110698 s r)). Qed.
Lemma lem4802975 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) : (term189 _110698 s r x y) = (term118 _110698 s r y x).
Proof. exact (eq_refl (term189 _110698 s r x y)). Qed.
Lemma lem4802976 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term190 _110698 s r x) = (term130 _110698 s r x).
Proof. exact (fun_ext (fun y : _110698 => @lem4802975 _110698 s r y x)). Qed.
Lemma lem4802977 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4802978 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term191 _110698 s r x) = (term131 _110698 s r x).
Proof. exact (MK_COMB (@lem4802977 _110698) (@lem4802976 _110698 s r x)). Qed.
Lemma lem4802979 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4802980 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term192 _110698 s r x) = (term167 _110698 s r x).
Proof. exact (MK_COMB (@lem4802979) (@lem4802978 _110698 s r x)). Qed.
Lemma lem4802981 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term193 _110698 s r y) = (term154 _110698 s r y).
Proof. exact (eq_refl (term193 _110698 s r y)). Qed.
Lemma lem4802982 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) : (term194 _110698 s r) = (term162 _110698 s r).
Proof. exact (fun_ext (fun y : _110698 => @lem4802981 _110698 s r y)). Qed.
Lemma lem4802983 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4802984 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) : (term195 _110698 s r) = (term163 _110698 s r).
Proof. exact (MK_COMB (@lem4802983 _110698) (@lem4802982 _110698 s r)). Qed.
Lemma lem4802985 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term187 _110698 x s r) = (term169 _110698 x s r).
Proof. exact (MK_COMB (@lem4802980 _110698 s r x) (@lem4802984 _110698 s r)). Qed.
Lemma lem4802986 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4802987 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term196 _110698 x s r) = (term197 _110698 x s r).
Proof. exact (MK_COMB (@lem4802986) (@lem4802985 _110698 x s r)). Qed.
Lemma lem4802988 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) : (term189 _110698 s r x y) = (term118 _110698 s r y x).
Proof. exact (eq_refl (term189 _110698 s r x y)). Qed.
Lemma lem4802989 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4802990 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) : (term198 _110698 s r x y) = (term199 _110698 s r y x).
Proof. exact (MK_COMB (@lem4802989) (@lem4802988 _110698 s r y x)). Qed.
Lemma lem4802991 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term193 _110698 s r y) = (term154 _110698 s r y).
Proof. exact (eq_refl (term193 _110698 s r y)). Qed.
Lemma lem4802992 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term200 _110698 x s r y) = (term201 _110698 x s r y).
Proof. exact (MK_COMB (@lem4802990 _110698 s r y x) (@lem4802991 _110698 s r y)). Qed.
Lemma lem4802993 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term202 _110698 x s r) = (term203 _110698 x s r).
Proof. exact (fun_ext (fun y : _110698 => @lem4802992 _110698 x s r y)). Qed.
Lemma lem4802994 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4802995 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term188 _110698 x s r) = (term204 _110698 x s r).
Proof. exact (MK_COMB (@lem4802994 _110698) (@lem4802993 _110698 x s r)). Qed.
Lemma lem4802996 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : ((term187 _110698 x s r) = (term188 _110698 x s r)) = ((term169 _110698 x s r) = (term204 _110698 x s r)).
Proof. exact (MK_COMB (@lem4802987 _110698 x s r) (@lem4802995 _110698 x s r)). Qed.
Lemma lem4802997 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term169 _110698 x s r) = (term204 _110698 x s r).
Proof. exact (EQ_MP (@lem4802996 _110698 x s r) (@lem4802974 _110698 x s r)). Qed.
Lemma lem4803000 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term205 _110698 x s r) = (term205 _110698 x s r).
Proof. exact (eq_refl (term205 _110698 x s r)). Qed.
Lemma lem4803001 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term205 _110698 x s r) = ((term169 _110698 x s r) = (term204 _110698 x s r)).
Proof. exact (eq_refl (term205 _110698 x s r)). Qed.
Lemma lem4803002 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term206 _110698 x s r) = (term206 _110698 x s r).
Proof. exact (eq_refl (term206 _110698 x s r)). Qed.
Lemma lem4803003 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : ((term205 _110698 x s r) = (term205 _110698 x s r)) = ((term205 _110698 x s r) = ((term169 _110698 x s r) = (term204 _110698 x s r))).
Proof. exact (MK_COMB (@lem4803002 _110698 x s r) (@lem4803001 _110698 x s r)). Qed.
Lemma lem4803004 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term205 _110698 x s r) = ((term169 _110698 x s r) = (term204 _110698 x s r)).
Proof. exact (eq_refl (term205 _110698 x s r)). Qed.
Lemma lem4803005 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4803006 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term206 _110698 x s r) = (term207 _110698 x s r).
Proof. exact (MK_COMB (@lem4803005) (@lem4803004 _110698 x s r)). Qed.
Lemma lem4803007 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : ((term169 _110698 x s r) = (term204 _110698 x s r)) = ((term169 _110698 x s r) = (term204 _110698 x s r)).
Proof. exact (eq_refl ((term169 _110698 x s r) = (term204 _110698 x s r))). Qed.
Lemma lem4803008 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : ((term205 _110698 x s r) = ((term169 _110698 x s r) = (term204 _110698 x s r))) = (((term169 _110698 x s r) = (term204 _110698 x s r)) = ((term169 _110698 x s r) = (term204 _110698 x s r))).
Proof. exact (MK_COMB (@lem4803006 _110698 x s r) (@lem4803007 _110698 x s r)). Qed.
Lemma lem4803009 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : ((term205 _110698 x s r) = (term205 _110698 x s r)) = (((term169 _110698 x s r) = (term204 _110698 x s r)) = ((term169 _110698 x s r) = (term204 _110698 x s r))).
Proof. exact (TRANS (@lem4803003 _110698 x s r) (@lem4803008 _110698 x s r)). Qed.
Lemma lem4803010 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : ((term169 _110698 x s r) = (term204 _110698 x s r)) = ((term169 _110698 x s r) = (term204 _110698 x s r)).
Proof. exact (EQ_MP (@lem4803009 _110698 x s r) (@lem4803000 _110698 x s r)). Qed.
Lemma lem4803011 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term169 _110698 x s r) = (term204 _110698 x s r).
Proof. exact (EQ_MP (@lem4803010 _110698 x s r) (@lem4802997 _110698 x s r)). Qed.
Lemma lem4803013 {A : Type'} (P : Prop) (Q : A -> Prop) : (term208 A P Q) = (term209 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4803014 {_110698 : Type'} (P : Prop) (Q : _110698 -> Prop) : (term208 _110698 P Q) = (term209 _110698 P Q).
Proof. exact (@lem4803013 _110698 P Q). Qed.
Lemma lem4803015 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term210 _110698 x s r y) = (term211 _110698 x s r y).
Proof. exact (@lem4803014 _110698 (term118 _110698 s r y x) (term153 _110698 s r y)). Qed.
Lemma lem4803016 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) : (term212 _110698 s r y y') = (term142 _110698 s r y y').
Proof. exact (eq_refl (term212 _110698 s r y y')). Qed.
Lemma lem4803017 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term213 _110698 s r y) = (term153 _110698 s r y).
Proof. exact (fun_ext (fun y' : _110698 => @lem4803016 _110698 s r y y')). Qed.
Lemma lem4803018 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4803019 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term214 _110698 s r y) = (term154 _110698 s r y).
Proof. exact (MK_COMB (@lem4803018 _110698) (@lem4803017 _110698 s r y)). Qed.
Lemma lem4803020 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) : (term199 _110698 s r y x) = (term199 _110698 s r y x).
Proof. exact (eq_refl (term199 _110698 s r y x)). Qed.
Lemma lem4803021 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term210 _110698 x s r y) = (term201 _110698 x s r y).
Proof. exact (MK_COMB (@lem4803020 _110698 s r y x) (@lem4803019 _110698 s r y)). Qed.
Lemma lem4803022 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4803023 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term215 _110698 x s r y) = (term216 _110698 x s r y).
Proof. exact (MK_COMB (@lem4803022) (@lem4803021 _110698 x s r y)). Qed.
Lemma lem4803024 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) : (term212 _110698 s r y y') = (term142 _110698 s r y y').
Proof. exact (eq_refl (term212 _110698 s r y y')). Qed.
Lemma lem4803025 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) : (term199 _110698 s r y x) = (term199 _110698 s r y x).
Proof. exact (eq_refl (term199 _110698 s r y x)). Qed.
Lemma lem4803026 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) : (term217 _110698 x s r y y') = (term218 _110698 x s r y y').
Proof. exact (MK_COMB (@lem4803025 _110698 s r y x) (@lem4803024 _110698 s r y y')). Qed.
Lemma lem4803027 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term219 _110698 x s r y) = (term220 _110698 x s r y).
Proof. exact (fun_ext (fun y' : _110698 => @lem4803026 _110698 x s r y y')). Qed.
Lemma lem4803028 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4803029 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term211 _110698 x s r y) = (term221 _110698 x s r y).
Proof. exact (MK_COMB (@lem4803028 _110698) (@lem4803027 _110698 x s r y)). Qed.
Lemma lem4803030 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : ((term210 _110698 x s r y) = (term211 _110698 x s r y)) = ((term201 _110698 x s r y) = (term221 _110698 x s r y)).
Proof. exact (MK_COMB (@lem4803023 _110698 x s r y) (@lem4803029 _110698 x s r y)). Qed.
Lemma lem4803031 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term201 _110698 x s r y) = (term221 _110698 x s r y).
Proof. exact (EQ_MP (@lem4803030 _110698 x s r y) (@lem4803015 _110698 x s r y)). Qed.
Lemma lem4803032 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term203 _110698 x s r) = (term222 _110698 x s r).
Proof. exact (fun_ext (fun y : _110698 => @lem4803031 _110698 x s r y)). Qed.
Lemma lem4803033 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4803034 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term204 _110698 x s r) = (term223 _110698 x s r).
Proof. exact (MK_COMB (@lem4803033 _110698) (@lem4803032 _110698 x s r)). Qed.
Lemma lem4803035 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term169 _110698 x s r) = (term223 _110698 x s r).
Proof. exact (TRANS (@lem4803011 _110698 x s r) (@lem4803034 _110698 x s r)). Qed.
Lemma lem4803036 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term178 _110698 x s r) = (term178 _110698 x s r).
Proof. exact (eq_refl (term178 _110698 x s r)). Qed.
Lemma lem4803037 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term180 _110698 x s r) = (term224 _110698 x s r).
Proof. exact (MK_COMB (@lem4803036 _110698 x s r) (@lem4803035 _110698 x s r)). Qed.
Lemma lem4803039 {A : Type'} (P : Prop) (Q : A -> Prop) : (term225 A P Q) = (term226 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4803040 {_110698 : Type'} (P : Prop) (Q : _110698 -> Prop) : (term225 _110698 P Q) = (term226 _110698 P Q).
Proof. exact (@lem4803039 _110698 P Q). Qed.
Lemma lem4803041 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term227 _110698 x s r) = (term228 _110698 x s r).
Proof. exact (@lem4803040 _110698 (term108 _110698 x s r) (term222 _110698 x s r)). Qed.
Lemma lem4803042 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term229 _110698 x s r y) = (term221 _110698 x s r y).
Proof. exact (eq_refl (term229 _110698 x s r y)). Qed.
Lemma lem4803043 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term230 _110698 x s r) = (term222 _110698 x s r).
Proof. exact (fun_ext (fun y : _110698 => @lem4803042 _110698 x s r y)). Qed.
Lemma lem4803044 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4803045 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term231 _110698 x s r) = (term223 _110698 x s r).
Proof. exact (MK_COMB (@lem4803044 _110698) (@lem4803043 _110698 x s r)). Qed.
Lemma lem4803046 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term178 _110698 x s r) = (term178 _110698 x s r).
Proof. exact (eq_refl (term178 _110698 x s r)). Qed.
Lemma lem4803047 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term227 _110698 x s r) = (term224 _110698 x s r).
Proof. exact (MK_COMB (@lem4803046 _110698 x s r) (@lem4803045 _110698 x s r)). Qed.
Lemma lem4803048 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4803049 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term232 _110698 x s r) = (term233 _110698 x s r).
Proof. exact (MK_COMB (@lem4803048) (@lem4803047 _110698 x s r)). Qed.
Lemma lem4803050 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term229 _110698 x s r y) = (term221 _110698 x s r y).
Proof. exact (eq_refl (term229 _110698 x s r y)). Qed.
Lemma lem4803051 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term178 _110698 x s r) = (term178 _110698 x s r).
Proof. exact (eq_refl (term178 _110698 x s r)). Qed.
Lemma lem4803052 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term234 _110698 x s r y) = (term235 _110698 x s r y).
Proof. exact (MK_COMB (@lem4803051 _110698 x s r) (@lem4803050 _110698 x s r y)). Qed.
Lemma lem4803053 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term236 _110698 x s r) = (term237 _110698 x s r).
Proof. exact (fun_ext (fun y : _110698 => @lem4803052 _110698 x s r y)). Qed.
Lemma lem4803054 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4803055 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term228 _110698 x s r) = (term238 _110698 x s r).
Proof. exact (MK_COMB (@lem4803054 _110698) (@lem4803053 _110698 x s r)). Qed.
Lemma lem4803056 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : ((term227 _110698 x s r) = (term228 _110698 x s r)) = ((term224 _110698 x s r) = (term238 _110698 x s r)).
Proof. exact (MK_COMB (@lem4803049 _110698 x s r) (@lem4803055 _110698 x s r)). Qed.
Lemma lem4803057 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term224 _110698 x s r) = (term238 _110698 x s r).
Proof. exact (EQ_MP (@lem4803056 _110698 x s r) (@lem4803041 _110698 x s r)). Qed.
Lemma lem4803059 {A : Type'} (P : Prop) (Q : A -> Prop) : (term225 A P Q) = (term226 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4803060 {_110698 : Type'} (P : Prop) (Q : _110698 -> Prop) : (term225 _110698 P Q) = (term226 _110698 P Q).
Proof. exact (@lem4803059 _110698 P Q). Qed.
Lemma lem4803061 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term239 _110698 x s r y) = (term240 _110698 x s r y).
Proof. exact (@lem4803060 _110698 (term108 _110698 x s r) (term220 _110698 x s r y)). Qed.
Lemma lem4803062 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) : (term241 _110698 x s r y y') = (term218 _110698 x s r y y').
Proof. exact (eq_refl (term241 _110698 x s r y y')). Qed.
Lemma lem4803063 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term242 _110698 x s r y) = (term220 _110698 x s r y).
Proof. exact (fun_ext (fun y' : _110698 => @lem4803062 _110698 x s r y y')). Qed.
Lemma lem4803064 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4803065 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term243 _110698 x s r y) = (term221 _110698 x s r y).
Proof. exact (MK_COMB (@lem4803064 _110698) (@lem4803063 _110698 x s r y)). Qed.
Lemma lem4803066 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term178 _110698 x s r) = (term178 _110698 x s r).
Proof. exact (eq_refl (term178 _110698 x s r)). Qed.
Lemma lem4803067 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term239 _110698 x s r y) = (term235 _110698 x s r y).
Proof. exact (MK_COMB (@lem4803066 _110698 x s r) (@lem4803065 _110698 x s r y)). Qed.
Lemma lem4803068 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4803069 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term244 _110698 x s r y) = (term245 _110698 x s r y).
Proof. exact (MK_COMB (@lem4803068) (@lem4803067 _110698 x s r y)). Qed.
Lemma lem4803070 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) : (term241 _110698 x s r y y') = (term218 _110698 x s r y y').
Proof. exact (eq_refl (term241 _110698 x s r y y')). Qed.
Lemma lem4803071 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term178 _110698 x s r) = (term178 _110698 x s r).
Proof. exact (eq_refl (term178 _110698 x s r)). Qed.
Lemma lem4803072 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) : (term246 _110698 x s r y y') = (term247 _110698 x s r y y').
Proof. exact (MK_COMB (@lem4803071 _110698 x s r) (@lem4803070 _110698 x s r y y')). Qed.
Lemma lem4803073 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term248 _110698 x s r y) = (term249 _110698 x s r y).
Proof. exact (fun_ext (fun y' : _110698 => @lem4803072 _110698 x s r y y')). Qed.
Lemma lem4803074 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4803075 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term240 _110698 x s r y) = (term250 _110698 x s r y).
Proof. exact (MK_COMB (@lem4803074 _110698) (@lem4803073 _110698 x s r y)). Qed.
Lemma lem4803076 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : ((term239 _110698 x s r y) = (term240 _110698 x s r y)) = ((term235 _110698 x s r y) = (term250 _110698 x s r y)).
Proof. exact (MK_COMB (@lem4803069 _110698 x s r y) (@lem4803075 _110698 x s r y)). Qed.
Lemma lem4803077 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term235 _110698 x s r y) = (term250 _110698 x s r y).
Proof. exact (EQ_MP (@lem4803076 _110698 x s r y) (@lem4803061 _110698 x s r y)). Qed.
Lemma lem4803078 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term237 _110698 x s r) = (term251 _110698 x s r).
Proof. exact (fun_ext (fun y : _110698 => @lem4803077 _110698 x s r y)). Qed.
Lemma lem4803079 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4803080 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term238 _110698 x s r) = (term252 _110698 x s r).
Proof. exact (MK_COMB (@lem4803079 _110698) (@lem4803078 _110698 x s r)). Qed.
Lemma lem4803081 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term224 _110698 x s r) = (term252 _110698 x s r).
Proof. exact (TRANS (@lem4803057 _110698 x s r) (@lem4803080 _110698 x s r)). Qed.
Lemma lem4803082 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term180 _110698 x s r) = (term252 _110698 x s r).
Proof. exact (TRANS (@lem4803037 _110698 x s r) (@lem4803081 _110698 x s r)). Qed.
Lemma lem4803083 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4803084 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term182 _110698 x s r) = (term253 _110698 x s r).
Proof. exact (MK_COMB (@lem4803083) (@lem4803082 _110698 x s r)). Qed.
Lemma lem4803086 {A : Type'} (P : A -> Prop) (Q : Prop) : (term254 A P Q) = (term255 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4803087 {_110698 : Type'} (P : _110698 -> Prop) (Q : Prop) : (term254 _110698 P Q) = (term255 _110698 P Q).
Proof. exact (@lem4803086 _110698 P Q). Qed.
Lemma lem4803088 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term256 _110698 x s r) = (term257 _110698 x s r).
Proof. exact (@lem4803087 _110698 (term105 _110698 x s r) (term172 _110698 x s r)). Qed.
Lemma lem4803089 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term258 _110698 x s r x') = (term97 _110698 x s r x').
Proof. exact (eq_refl (term258 _110698 x s r x')). Qed.
Lemma lem4803090 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term259 _110698 x s r) = (term105 _110698 x s r).
Proof. exact (fun_ext (fun x' : _110698 => @lem4803089 _110698 x s r x')). Qed.
Lemma lem4803091 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4803092 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term260 _110698 x s r) = (term106 _110698 x s r).
Proof. exact (MK_COMB (@lem4803091 _110698) (@lem4803090 _110698 x s r)). Qed.
Lemma lem4803093 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4803094 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term261 _110698 x s r) = (term174 _110698 x s r).
Proof. exact (MK_COMB (@lem4803093) (@lem4803092 _110698 x s r)). Qed.
Lemma lem4803095 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term172 _110698 x s r) = (term172 _110698 x s r).
Proof. exact (eq_refl (term172 _110698 x s r)). Qed.
Lemma lem4803096 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term256 _110698 x s r) = (term176 _110698 x s r).
Proof. exact (MK_COMB (@lem4803094 _110698 x s r) (@lem4803095 _110698 x s r)). Qed.
Lemma lem4803097 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4803098 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term262 _110698 x s r) = (term263 _110698 x s r).
Proof. exact (MK_COMB (@lem4803097) (@lem4803096 _110698 x s r)). Qed.
Lemma lem4803099 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term258 _110698 x s r x') = (term97 _110698 x s r x').
Proof. exact (eq_refl (term258 _110698 x s r x')). Qed.
Lemma lem4803100 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4803101 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term264 _110698 x s r x') = (term265 _110698 x s r x').
Proof. exact (MK_COMB (@lem4803100) (@lem4803099 _110698 x s r x')). Qed.
Lemma lem4803102 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term172 _110698 x s r) = (term172 _110698 x s r).
Proof. exact (eq_refl (term172 _110698 x s r)). Qed.
Lemma lem4803103 {_110698 : Type'} (x' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term266 _110698 x' x s r) = (term267 _110698 x' x s r).
Proof. exact (MK_COMB (@lem4803101 _110698 x s r x') (@lem4803102 _110698 x s r)). Qed.
Lemma lem4803104 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term268 _110698 x s r) = (term269 _110698 x s r).
Proof. exact (fun_ext (fun x' : _110698 => @lem4803103 _110698 x' x s r)). Qed.
Lemma lem4803105 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4803106 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term257 _110698 x s r) = (term270 _110698 x s r).
Proof. exact (MK_COMB (@lem4803105 _110698) (@lem4803104 _110698 x s r)). Qed.
Lemma lem4803107 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : ((term256 _110698 x s r) = (term257 _110698 x s r)) = ((term176 _110698 x s r) = (term270 _110698 x s r)).
Proof. exact (MK_COMB (@lem4803098 _110698 x s r) (@lem4803106 _110698 x s r)). Qed.
Lemma lem4803108 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term176 _110698 x s r) = (term270 _110698 x s r).
Proof. exact (EQ_MP (@lem4803107 _110698 x s r) (@lem4803088 _110698 x s r)). Qed.
Lemma lem4803110 {A : Type'} (P : A -> Prop) (Q : Prop) : (term254 A P Q) = (term255 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4803111 {_110698 : Type'} (P : _110698 -> Prop) (Q : Prop) : (term254 _110698 P Q) = (term255 _110698 P Q).
Proof. exact (@lem4803110 _110698 P Q). Qed.
Lemma lem4803112 {_110698 : Type'} (x' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term271 _110698 x' x s r) = (term272 _110698 x' x s r).
Proof. exact (@lem4803111 _110698 (term96 _110698 x s r x') (term172 _110698 x s r)). Qed.
Lemma lem4803113 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term273 _110698 x s r x' y) = (term84 _110698 x s r x' y).
Proof. exact (eq_refl (term273 _110698 x s r x' y)). Qed.
Lemma lem4803114 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term274 _110698 x s r x') = (term96 _110698 x s r x').
Proof. exact (fun_ext (fun y : _110698 => @lem4803113 _110698 x s r x' y)). Qed.
Lemma lem4803115 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4803116 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term275 _110698 x s r x') = (term97 _110698 x s r x').
Proof. exact (MK_COMB (@lem4803115 _110698) (@lem4803114 _110698 x s r x')). Qed.
Lemma lem4803117 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4803118 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term276 _110698 x s r x') = (term265 _110698 x s r x').
Proof. exact (MK_COMB (@lem4803117) (@lem4803116 _110698 x s r x')). Qed.
Lemma lem4803119 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term172 _110698 x s r) = (term172 _110698 x s r).
Proof. exact (eq_refl (term172 _110698 x s r)). Qed.
Lemma lem4803120 {_110698 : Type'} (x' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term271 _110698 x' x s r) = (term267 _110698 x' x s r).
Proof. exact (MK_COMB (@lem4803118 _110698 x s r x') (@lem4803119 _110698 x s r)). Qed.
Lemma lem4803121 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4803122 {_110698 : Type'} (x' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term277 _110698 x' x s r) = (term278 _110698 x' x s r).
Proof. exact (MK_COMB (@lem4803121) (@lem4803120 _110698 x' x s r)). Qed.
Lemma lem4803123 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term273 _110698 x s r x' y) = (term84 _110698 x s r x' y).
Proof. exact (eq_refl (term273 _110698 x s r x' y)). Qed.
Lemma lem4803124 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4803125 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term279 _110698 x s r x' y) = (term280 _110698 x s r x' y).
Proof. exact (MK_COMB (@lem4803124) (@lem4803123 _110698 x s r x' y)). Qed.
Lemma lem4803126 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term172 _110698 x s r) = (term172 _110698 x s r).
Proof. exact (eq_refl (term172 _110698 x s r)). Qed.
Lemma lem4803127 {_110698 : Type'} (x' : _110698) (y : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term281 _110698 x' y x s r) = (term282 _110698 x' y x s r).
Proof. exact (MK_COMB (@lem4803125 _110698 x s r x' y) (@lem4803126 _110698 x s r)). Qed.
Lemma lem4803128 {_110698 : Type'} (x' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term283 _110698 x' x s r) = (term284 _110698 x' x s r).
Proof. exact (fun_ext (fun y : _110698 => @lem4803127 _110698 x' y x s r)). Qed.
Lemma lem4803129 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4803130 {_110698 : Type'} (x' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term272 _110698 x' x s r) = (term285 _110698 x' x s r).
Proof. exact (MK_COMB (@lem4803129 _110698) (@lem4803128 _110698 x' x s r)). Qed.
Lemma lem4803131 {_110698 : Type'} (x' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : ((term271 _110698 x' x s r) = (term272 _110698 x' x s r)) = ((term267 _110698 x' x s r) = (term285 _110698 x' x s r)).
Proof. exact (MK_COMB (@lem4803122 _110698 x' x s r) (@lem4803130 _110698 x' x s r)). Qed.
Lemma lem4803132 {_110698 : Type'} (x' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term267 _110698 x' x s r) = (term285 _110698 x' x s r).
Proof. exact (EQ_MP (@lem4803131 _110698 x' x s r) (@lem4803112 _110698 x' x s r)). Qed.
Lemma lem4803133 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term269 _110698 x s r) = (term286 _110698 x s r).
Proof. exact (fun_ext (fun x' : _110698 => @lem4803132 _110698 x' x s r)). Qed.
Lemma lem4803134 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4803135 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term270 _110698 x s r) = (term287 _110698 x s r).
Proof. exact (MK_COMB (@lem4803134 _110698) (@lem4803133 _110698 x s r)). Qed.
Lemma lem4803136 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term176 _110698 x s r) = (term287 _110698 x s r).
Proof. exact (TRANS (@lem4803108 _110698 x s r) (@lem4803135 _110698 x s r)). Qed.
Lemma lem4803137 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term184 _110698 x s r) = (term288 _110698 x s r).
Proof. exact (MK_COMB (@lem4803084 _110698 x s r) (@lem4803136 _110698 x s r)). Qed.
Lemma lem4803139 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term185 A P Q) = (term186 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4803140 {_110698 : Type'} (P : _110698 -> Prop) (Q : _110698 -> Prop) : (term185 _110698 P Q) = (term186 _110698 P Q).
Proof. exact (@lem4803139 _110698 P Q). Qed.
Lemma lem4803141 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term289 _110698 x s r) = (term290 _110698 x s r).
Proof. exact (@lem4803140 _110698 (term251 _110698 x s r) (term286 _110698 x s r)). Qed.
Lemma lem4803142 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term291 _110698 x s r y) = (term250 _110698 x s r y).
Proof. exact (eq_refl (term291 _110698 x s r y)). Qed.
Lemma lem4803143 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term292 _110698 x s r) = (term251 _110698 x s r).
Proof. exact (fun_ext (fun y : _110698 => @lem4803142 _110698 x s r y)). Qed.
Lemma lem4803144 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4803145 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term293 _110698 x s r) = (term252 _110698 x s r).
Proof. exact (MK_COMB (@lem4803144 _110698) (@lem4803143 _110698 x s r)). Qed.
Lemma lem4803146 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4803147 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term294 _110698 x s r) = (term253 _110698 x s r).
Proof. exact (MK_COMB (@lem4803146) (@lem4803145 _110698 x s r)). Qed.
Lemma lem4803148 {_110698 : Type'} (y : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term295 _110698 x s r y) = (term285 _110698 y x s r).
Proof. exact (eq_refl (term295 _110698 x s r y)). Qed.
Lemma lem4803149 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term296 _110698 x s r) = (term286 _110698 x s r).
Proof. exact (fun_ext (fun y : _110698 => @lem4803148 _110698 y x s r)). Qed.
Lemma lem4803150 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4803151 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term297 _110698 x s r) = (term287 _110698 x s r).
Proof. exact (MK_COMB (@lem4803150 _110698) (@lem4803149 _110698 x s r)). Qed.
Lemma lem4803152 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term289 _110698 x s r) = (term288 _110698 x s r).
Proof. exact (MK_COMB (@lem4803147 _110698 x s r) (@lem4803151 _110698 x s r)). Qed.
Lemma lem4803153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4803154 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term298 _110698 x s r) = (term299 _110698 x s r).
Proof. exact (MK_COMB (@lem4803153) (@lem4803152 _110698 x s r)). Qed.
Lemma lem4803155 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term291 _110698 x s r y) = (term250 _110698 x s r y).
Proof. exact (eq_refl (term291 _110698 x s r y)). Qed.
Lemma lem4803156 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4803157 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term300 _110698 x s r y) = (term301 _110698 x s r y).
Proof. exact (MK_COMB (@lem4803156) (@lem4803155 _110698 x s r y)). Qed.
Lemma lem4803158 {_110698 : Type'} (y : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term295 _110698 x s r y) = (term285 _110698 y x s r).
Proof. exact (eq_refl (term295 _110698 x s r y)). Qed.
Lemma lem4803159 {_110698 : Type'} (y : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term302 _110698 x s r y) = (term303 _110698 y x s r).
Proof. exact (MK_COMB (@lem4803157 _110698 x s r y) (@lem4803158 _110698 y x s r)). Qed.
Lemma lem4803160 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term304 _110698 x s r) = (term305 _110698 x s r).
Proof. exact (fun_ext (fun y : _110698 => @lem4803159 _110698 y x s r)). Qed.
Lemma lem4803161 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4803162 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term290 _110698 x s r) = (term306 _110698 x s r).
Proof. exact (MK_COMB (@lem4803161 _110698) (@lem4803160 _110698 x s r)). Qed.
Lemma lem4803163 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : ((term289 _110698 x s r) = (term290 _110698 x s r)) = ((term288 _110698 x s r) = (term306 _110698 x s r)).
Proof. exact (MK_COMB (@lem4803154 _110698 x s r) (@lem4803162 _110698 x s r)). Qed.
Lemma lem4803164 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term288 _110698 x s r) = (term306 _110698 x s r).
Proof. exact (EQ_MP (@lem4803163 _110698 x s r) (@lem4803141 _110698 x s r)). Qed.
Lemma lem4803167 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term307 _110698 x s r) = (term307 _110698 x s r).
Proof. exact (eq_refl (term307 _110698 x s r)). Qed.
Lemma lem4803168 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term307 _110698 x s r) = ((term288 _110698 x s r) = (term306 _110698 x s r)).
Proof. exact (eq_refl (term307 _110698 x s r)). Qed.
Lemma lem4803169 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term308 _110698 x s r) = (term308 _110698 x s r).
Proof. exact (eq_refl (term308 _110698 x s r)). Qed.
Lemma lem4803170 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : ((term307 _110698 x s r) = (term307 _110698 x s r)) = ((term307 _110698 x s r) = ((term288 _110698 x s r) = (term306 _110698 x s r))).
Proof. exact (MK_COMB (@lem4803169 _110698 x s r) (@lem4803168 _110698 x s r)). Qed.
Lemma lem4803171 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term307 _110698 x s r) = ((term288 _110698 x s r) = (term306 _110698 x s r)).
Proof. exact (eq_refl (term307 _110698 x s r)). Qed.
Lemma lem4803172 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4803173 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term308 _110698 x s r) = (term309 _110698 x s r).
Proof. exact (MK_COMB (@lem4803172) (@lem4803171 _110698 x s r)). Qed.
Lemma lem4803174 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : ((term288 _110698 x s r) = (term306 _110698 x s r)) = ((term288 _110698 x s r) = (term306 _110698 x s r)).
Proof. exact (eq_refl ((term288 _110698 x s r) = (term306 _110698 x s r))). Qed.
Lemma lem4803175 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : ((term307 _110698 x s r) = ((term288 _110698 x s r) = (term306 _110698 x s r))) = (((term288 _110698 x s r) = (term306 _110698 x s r)) = ((term288 _110698 x s r) = (term306 _110698 x s r))).
Proof. exact (MK_COMB (@lem4803173 _110698 x s r) (@lem4803174 _110698 x s r)). Qed.
Lemma lem4803176 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : ((term307 _110698 x s r) = (term307 _110698 x s r)) = (((term288 _110698 x s r) = (term306 _110698 x s r)) = ((term288 _110698 x s r) = (term306 _110698 x s r))).
Proof. exact (TRANS (@lem4803170 _110698 x s r) (@lem4803175 _110698 x s r)). Qed.
Lemma lem4803177 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : ((term288 _110698 x s r) = (term306 _110698 x s r)) = ((term288 _110698 x s r) = (term306 _110698 x s r)).
Proof. exact (EQ_MP (@lem4803176 _110698 x s r) (@lem4803167 _110698 x s r)). Qed.
Lemma lem4803178 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term288 _110698 x s r) = (term306 _110698 x s r).
Proof. exact (EQ_MP (@lem4803177 _110698 x s r) (@lem4803164 _110698 x s r)). Qed.
Lemma lem4803180 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term185 A P Q) = (term186 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4803181 {_110698 : Type'} (P : _110698 -> Prop) (Q : _110698 -> Prop) : (term185 _110698 P Q) = (term186 _110698 P Q).
Proof. exact (@lem4803180 _110698 P Q). Qed.
Lemma lem4803182 {_110698 : Type'} (y : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term310 _110698 y x s r) = (term311 _110698 y x s r).
Proof. exact (@lem4803181 _110698 (term249 _110698 x s r y) (term284 _110698 y x s r)). Qed.
Lemma lem4803183 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) : (term312 _110698 x s r y y') = (term247 _110698 x s r y y').
Proof. exact (eq_refl (term312 _110698 x s r y y')). Qed.
Lemma lem4803184 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term313 _110698 x s r y) = (term249 _110698 x s r y).
Proof. exact (fun_ext (fun y' : _110698 => @lem4803183 _110698 x s r y y')). Qed.
Lemma lem4803185 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4803186 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term314 _110698 x s r y) = (term250 _110698 x s r y).
Proof. exact (MK_COMB (@lem4803185 _110698) (@lem4803184 _110698 x s r y)). Qed.
Lemma lem4803187 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4803188 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) : (term315 _110698 x s r y) = (term301 _110698 x s r y).
Proof. exact (MK_COMB (@lem4803187) (@lem4803186 _110698 x s r y)). Qed.
Lemma lem4803189 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term316 _110698 y x s r y') = (term282 _110698 y y' x s r).
Proof. exact (eq_refl (term316 _110698 y x s r y')). Qed.
Lemma lem4803190 {_110698 : Type'} (y : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term317 _110698 y x s r) = (term284 _110698 y x s r).
Proof. exact (fun_ext (fun y' : _110698 => @lem4803189 _110698 y y' x s r)). Qed.
Lemma lem4803191 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4803192 {_110698 : Type'} (y : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term318 _110698 y x s r) = (term285 _110698 y x s r).
Proof. exact (MK_COMB (@lem4803191 _110698) (@lem4803190 _110698 y x s r)). Qed.
Lemma lem4803193 {_110698 : Type'} (y : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term310 _110698 y x s r) = (term303 _110698 y x s r).
Proof. exact (MK_COMB (@lem4803188 _110698 x s r y) (@lem4803192 _110698 y x s r)). Qed.
Lemma lem4803194 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4803195 {_110698 : Type'} (y : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term319 _110698 y x s r) = (term320 _110698 y x s r).
Proof. exact (MK_COMB (@lem4803194) (@lem4803193 _110698 y x s r)). Qed.
Lemma lem4803196 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) : (term312 _110698 x s r y y') = (term247 _110698 x s r y y').
Proof. exact (eq_refl (term312 _110698 x s r y y')). Qed.
Lemma lem4803197 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4803198 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) : (term321 _110698 x s r y y') = (term322 _110698 x s r y y').
Proof. exact (MK_COMB (@lem4803197) (@lem4803196 _110698 x s r y y')). Qed.
Lemma lem4803199 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term316 _110698 y x s r y') = (term282 _110698 y y' x s r).
Proof. exact (eq_refl (term316 _110698 y x s r y')). Qed.
Lemma lem4803200 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term323 _110698 y x s r y') = (term324 _110698 y y' x s r).
Proof. exact (MK_COMB (@lem4803198 _110698 x s r y y') (@lem4803199 _110698 y y' x s r)). Qed.
Lemma lem4803201 {_110698 : Type'} (y : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term325 _110698 y x s r) = (term326 _110698 y x s r).
Proof. exact (fun_ext (fun y' : _110698 => @lem4803200 _110698 y y' x s r)). Qed.
Lemma lem4803202 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4803203 {_110698 : Type'} (y : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term311 _110698 y x s r) = (term327 _110698 y x s r).
Proof. exact (MK_COMB (@lem4803202 _110698) (@lem4803201 _110698 y x s r)). Qed.
Lemma lem4803204 {_110698 : Type'} (y : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : ((term310 _110698 y x s r) = (term311 _110698 y x s r)) = ((term303 _110698 y x s r) = (term327 _110698 y x s r)).
Proof. exact (MK_COMB (@lem4803195 _110698 y x s r) (@lem4803203 _110698 y x s r)). Qed.
Lemma lem4803205 {_110698 : Type'} (y : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term303 _110698 y x s r) = (term327 _110698 y x s r).
Proof. exact (EQ_MP (@lem4803204 _110698 y x s r) (@lem4803182 _110698 y x s r)). Qed.
Lemma lem4803206 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term305 _110698 x s r) = (term328 _110698 x s r).
Proof. exact (fun_ext (fun y : _110698 => @lem4803205 _110698 y x s r)). Qed.
Lemma lem4803207 {_110698 : Type'} : (@ex _110698) = (@ex _110698).
Proof. exact (eq_refl (@ex _110698)). Qed.
Lemma lem4803208 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term306 _110698 x s r) = (term329 _110698 x s r).
Proof. exact (MK_COMB (@lem4803207 _110698) (@lem4803206 _110698 x s r)). Qed.
Lemma lem4803209 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term288 _110698 x s r) = (term329 _110698 x s r).
Proof. exact (TRANS (@lem4803178 _110698 x s r) (@lem4803208 _110698 x s r)). Qed.
Lemma lem4803211 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term184 _110698 x s r) = (term329 _110698 x s r).
Proof. exact (TRANS (@lem4803137 _110698 x s r) (@lem4803209 _110698 x s r)). Qed.
Lemma lem4803212 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term71 _110698 x s r) = (term329 _110698 x s r).
Proof. exact (TRANS (@lem4802665 _110698 x s r) (@lem4803211 _110698 x s r)). Qed.
Lemma lem4803213 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term71 _110698 x s r) : term329 _110698 x s r.
Proof. exact (EQ_MP (@lem4803212 _110698 x s r) (@lem4802453 _110698 x s r h1)). Qed.
Lemma lem4803214 {_110698 : Type'} (y : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term327 _110698 y x s r) : term327 _110698 y x s r.
Proof. exact (h1). Qed.
Lemma lem4803215 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term324 _110698 y y' x s r) : term324 _110698 y y' x s r.
Proof. exact (h1). Qed.
Lemma lem4803248 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) (y : _110698) : (term147 _110698 s r x y) = (term147 _110698 s r x y).
Proof. exact (eq_refl (term147 _110698 s r x y)). Qed.
Lemma lem4803249 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term155 _110698 s r x) = (term155 _110698 s r x).
Proof. exact (fun_ext (fun y : _110698 => @lem4803248 _110698 s r x y)). Qed.
Lemma lem4803250 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4803251 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term156 _110698 s r x) = (term156 _110698 s r x).
Proof. exact (MK_COMB (@lem4803250 _110698) (@lem4803249 _110698 s r x)). Qed.
Lemma lem4803252 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) : (term164 _110698 s r) = (term164 _110698 s r).
Proof. exact (fun_ext (fun x : _110698 => @lem4803251 _110698 s r x)). Qed.
Lemma lem4803253 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4803254 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) : (term165 _110698 s r) = (term165 _110698 s r).
Proof. exact (MK_COMB (@lem4803253 _110698) (@lem4803252 _110698 s r)). Qed.
Lemma lem4803285 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) : (term124 _110698 s r y x) = (term124 _110698 s r y x).
Proof. exact (eq_refl (term124 _110698 s r y x)). Qed.
Lemma lem4803286 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term132 _110698 s r x) = (term132 _110698 s r x).
Proof. exact (fun_ext (fun y : _110698 => @lem4803285 _110698 s r y x)). Qed.
Lemma lem4803287 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4803288 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term133 _110698 s r x) = (term133 _110698 s r x).
Proof. exact (MK_COMB (@lem4803287 _110698) (@lem4803286 _110698 s r x)). Qed.
Lemma lem4803289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4803290 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term171 _110698 s r x) = (term171 _110698 s r x).
Proof. exact (MK_COMB (@lem4803289) (@lem4803288 _110698 s r x)). Qed.
Lemma lem4803291 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term172 _110698 x s r) = (term172 _110698 x s r).
Proof. exact (MK_COMB (@lem4803290 _110698 s r x) (@lem4803254 _110698 s r)). Qed.
Lemma lem4803342 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) : (term280 _110698 x s r y y') = (term280 _110698 x s r y y').
Proof. exact (eq_refl (term280 _110698 x s r y y')). Qed.
Lemma lem4803343 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term282 _110698 y y' x s r) = (term282 _110698 y y' x s r).
Proof. exact (MK_COMB (@lem4803342 _110698 x s r y y') (@lem4803291 _110698 x s r)). Qed.
Lemma lem4803414 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) : (term218 _110698 x s r y y') = (term218 _110698 x s r y y').
Proof. exact (eq_refl (term218 _110698 x s r y y')). Qed.
Lemma lem4803467 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term88 _110698 x s r x' y) = (term88 _110698 x s r x' y).
Proof. exact (eq_refl (term88 _110698 x s r x' y)). Qed.
Lemma lem4803468 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term98 _110698 x s r x') = (term98 _110698 x s r x').
Proof. exact (fun_ext (fun y : _110698 => @lem4803467 _110698 x s r x' y)). Qed.
Lemma lem4803469 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4803470 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term99 _110698 x s r x') = (term99 _110698 x s r x').
Proof. exact (MK_COMB (@lem4803469 _110698) (@lem4803468 _110698 x s r x')). Qed.
Lemma lem4803471 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term107 _110698 x s r) = (term107 _110698 x s r).
Proof. exact (fun_ext (fun x' : _110698 => @lem4803470 _110698 x s r x')). Qed.
Lemma lem4803472 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4803473 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term108 _110698 x s r) = (term108 _110698 x s r).
Proof. exact (MK_COMB (@lem4803472 _110698) (@lem4803471 _110698 x s r)). Qed.
Lemma lem4803474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4803475 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term178 _110698 x s r) = (term178 _110698 x s r).
Proof. exact (MK_COMB (@lem4803474) (@lem4803473 _110698 x s r)). Qed.
Lemma lem4803476 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) : (term247 _110698 x s r y y') = (term247 _110698 x s r y y').
Proof. exact (MK_COMB (@lem4803475 _110698 x s r) (@lem4803414 _110698 x s r y y')). Qed.
Lemma lem4803477 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4803478 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) : (term322 _110698 x s r y y') = (term322 _110698 x s r y y').
Proof. exact (MK_COMB (@lem4803477) (@lem4803476 _110698 x s r y y')). Qed.
Lemma lem4803479 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term324 _110698 y y' x s r) = (term324 _110698 y y' x s r).
Proof. exact (MK_COMB (@lem4803478 _110698 x s r y y') (@lem4803343 _110698 y y' x s r)). Qed.
Lemma lem4803480 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term324 _110698 y y' x s r) : term324 _110698 y y' x s r.
Proof. exact (EQ_MP (@lem4803479 _110698 y y' x s r) (@lem4803215 _110698 y y' x s r h1)). Qed.
Lemma lem4803481 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term247 _110698 x s r y y'.
Proof. exact (h1). Qed.
Lemma lem4803482 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term282 _110698 y y' x s r.
Proof. exact (h1). Qed.
Lemma lem4803483 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term218 _110698 x s r y y'.
Proof. exact (proj2 (@lem4803481 _110698 x s r y y' h1)). Qed.
Lemma lem4803484 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term108 _110698 x s r.
Proof. exact (proj1 (@lem4803481 _110698 x s r y y' h1)). Qed.
Lemma lem4803485 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term118 _110698 s r y x) : term118 _110698 s r y x.
Proof. exact (h1). Qed.
Lemma lem4803486 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term142 _110698 s r y y') : term142 _110698 s r y y'.
Proof. exact (h1). Qed.
Lemma lem4803487 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term118 _110698 s r y x) : term114 _110698 r y x.
Proof. exact (proj2 (@lem4803485 _110698 s r y x h1)). Qed.
Lemma lem4803488 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term118 _110698 s r y x) : term120 _110698 s y x.
Proof. exact (proj1 (@lem4803485 _110698 s r y x h1)). Qed.
Lemma lem4803494 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term142 _110698 s r y y') : term143 _110698 s y y'.
Proof. exact (proj1 (@lem4803486 _110698 s r y y' h1)). Qed.
Lemma lem4803495 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term142 _110698 s r y y') : term140 _110698 s y y'.
Proof. exact (proj2 (@lem4803494 _110698 s r y y' h1)). Qed.
Lemma lem4803499 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term172 _110698 x s r.
Proof. exact (proj2 (@lem4803482 _110698 y y' x s r h1)). Qed.
Lemma lem4803500 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term84 _110698 x s r y y'.
Proof. exact (proj1 (@lem4803482 _110698 y y' x s r h1)). Qed.
Lemma lem4803501 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term165 _110698 s r.
Proof. exact (proj2 (@lem4803499 _110698 y y' x s r h1)). Qed.
Lemma lem4803502 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term133 _110698 s r x.
Proof. exact (proj1 (@lem4803499 _110698 y y' x s r h1)). Qed.
Lemma lem4803504 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term26 _110698 x s y y'.
Proof. exact (proj1 (@lem4803500 _110698 y y' x s r h1)). Qed.
Lemma lem4803505 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term24 _110698 x s y y'.
Proof. exact (proj2 (@lem4803504 _110698 y y' x s r h1)). Qed.
Lemma lem4803506 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term13 _110698 x y s.
Proof. exact (proj1 (@lem4803504 _110698 y y' x s r h1)). Qed.
Lemma lem4803508 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term13 _110698 x y' s.
Proof. exact (proj1 (@lem4803505 _110698 y y' x s r h1)). Qed.
Lemma lem4803516 {_110698 : Type'} (r : type1402 _110698) (x' : _110698) (y : _110698) : (r x' y) = (r x' y).
Proof. exact (eq_refl (r x' y)). Qed.
Lemma lem4803533 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term78 _110698 x s x' y) = (term330 _110698 x s x' y).
Proof. exact (@lem19699 (term22 _110698 y x) (term331 _110698 y s) (x' = y)). Qed.
Lemma lem4803540 {_110698 : Type'} (x : _110698) (x' : _110698) (s : _110698 -> Prop) : (term76 _110698 x x' s) = (term76 _110698 x x' s).
Proof. exact (eq_refl (term76 _110698 x x' s)). Qed.
Lemma lem4803541 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term81 _110698 x s x' y) = (term332 _110698 x s x' y).
Proof. exact (MK_COMB (@lem4803540 _110698 x x' s) (@lem4803533 _110698 x s x' y)). Qed.
Lemma lem4803542 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term332 _110698 x s x' y) = (term333 _110698 x s x' y).
Proof. exact (@lem19490 (term334 _110698 x x' y) (term73 _110698 x x' s) (term135 _110698 s x' y)). Qed.
Lemma lem4803549 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term335 _110698 x s x' y) = (term336 _110698 x s x' y).
Proof. exact (@lem19699 (term22 _110698 x' x) (term331 _110698 x' s) (term135 _110698 s x' y)). Qed.
Lemma lem4803556 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (x' : _110698) (y : _110698) : (term337 _110698 s x x' y) = (term338 _110698 s x x' y).
Proof. exact (@lem19699 (term22 _110698 x' x) (term331 _110698 x' s) (term334 _110698 x x' y)). Qed.
Lemma lem4803557 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4803558 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (x' : _110698) (y : _110698) : (term339 _110698 s x x' y) = (term340 _110698 s x x' y).
Proof. exact (MK_COMB (@lem4803557) (@lem4803556 _110698 s x x' y)). Qed.
Lemma lem4803559 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term333 _110698 x s x' y) = (term341 _110698 x s x' y).
Proof. exact (MK_COMB (@lem4803558 _110698 s x x' y) (@lem4803549 _110698 x s x' y)). Qed.
Lemma lem4803560 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term332 _110698 x s x' y) = (term341 _110698 x s x' y).
Proof. exact (TRANS (@lem4803542 _110698 x s x' y) (@lem4803559 _110698 x s x' y)). Qed.
Lemma lem4803561 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term81 _110698 x s x' y) = (term341 _110698 x s x' y).
Proof. exact (TRANS (@lem4803541 _110698 x s x' y) (@lem4803560 _110698 x s x' y)). Qed.
Lemma lem4803562 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4803563 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term86 _110698 x s x' y) = (term342 _110698 x s x' y).
Proof. exact (MK_COMB (@lem4803562) (@lem4803561 _110698 x s x' y)). Qed.
Lemma lem4803564 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term88 _110698 x s r x' y) = (term343 _110698 x s r x' y).
Proof. exact (MK_COMB (@lem4803563 _110698 x s x' y) (@lem4803516 _110698 r x' y)). Qed.
Lemma lem4803565 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term343 _110698 x s r x' y) = (term344 _110698 x s r x' y).
Proof. exact (@lem19699 (term338 _110698 s x x' y) (term336 _110698 x s x' y) (r x' y)). Qed.
Lemma lem4803572 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term345 _110698 x s r x' y) = (term346 _110698 x s r x' y).
Proof. exact (@lem19699 (term347 _110698 x s x' y) (term138 _110698 s x' y) (r x' y)). Qed.
Lemma lem4803579 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term348 _110698 s x r x' y) = (term349 _110698 s x r x' y).
Proof. exact (@lem19699 (term350 _110698 x x' y) (term351 _110698 s x x' y) (r x' y)). Qed.
Lemma lem4803580 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4803581 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term352 _110698 s x r x' y) = (term353 _110698 s x r x' y).
Proof. exact (MK_COMB (@lem4803580) (@lem4803579 _110698 s x r x' y)). Qed.
Lemma lem4803582 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term344 _110698 x s r x' y) = (term354 _110698 x s r x' y).
Proof. exact (MK_COMB (@lem4803581 _110698 s x r x' y) (@lem4803572 _110698 x s r x' y)). Qed.
Lemma lem4803583 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term343 _110698 x s r x' y) = (term354 _110698 x s r x' y).
Proof. exact (TRANS (@lem4803565 _110698 x s r x' y) (@lem4803582 _110698 x s r x' y)). Qed.
Lemma lem4803584 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term88 _110698 x s r x' y) = (term354 _110698 x s r x' y).
Proof. exact (TRANS (@lem4803564 _110698 x s r x' y) (@lem4803583 _110698 x s r x' y)). Qed.
Lemma lem4803585 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term98 _110698 x s r x') = (term355 _110698 x s r x').
Proof. exact (fun_ext (fun y : _110698 => @lem4803584 _110698 x s r x' y)). Qed.
Lemma lem4803586 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4803587 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term99 _110698 x s r x') = (term356 _110698 x s r x').
Proof. exact (MK_COMB (@lem4803586 _110698) (@lem4803585 _110698 x s r x')). Qed.
Lemma lem4803588 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term107 _110698 x s r) = (term357 _110698 x s r).
Proof. exact (fun_ext (fun x' : _110698 => @lem4803587 _110698 x s r x')). Qed.
Lemma lem4803589 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4803591 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term108 _110698 x s r) = (term358 _110698 x s r).
Proof. exact (MK_COMB (@lem4803589 _110698) (@lem4803588 _110698 x s r)). Qed.
Lemma lem4803592 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term358 _110698 x s r.
Proof. exact (EQ_MP (@lem4803591 _110698 x s r) (@lem4803484 _110698 x s r y y' h1)). Qed.
Lemma lem4803604 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (y : _110698) (h1 : term359 _110698 r x y) : term359 _110698 r x y.
Proof. exact (h1). Qed.
Lemma lem4803606 {_110698 : Type'} (r : type1402 _110698) (x' : _110698) (y : _110698) : (r x' y) = (r x' y).
Proof. exact (eq_refl (r x' y)). Qed.
Lemma lem4803623 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term78 _110698 x s x' y) = (term330 _110698 x s x' y).
Proof. exact (@lem19699 (term22 _110698 y x) (term331 _110698 y s) (x' = y)). Qed.
Lemma lem4803630 {_110698 : Type'} (x : _110698) (x' : _110698) (s : _110698 -> Prop) : (term76 _110698 x x' s) = (term76 _110698 x x' s).
Proof. exact (eq_refl (term76 _110698 x x' s)). Qed.
Lemma lem4803631 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term81 _110698 x s x' y) = (term332 _110698 x s x' y).
Proof. exact (MK_COMB (@lem4803630 _110698 x x' s) (@lem4803623 _110698 x s x' y)). Qed.
Lemma lem4803632 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term332 _110698 x s x' y) = (term333 _110698 x s x' y).
Proof. exact (@lem19490 (term334 _110698 x x' y) (term73 _110698 x x' s) (term135 _110698 s x' y)). Qed.
Lemma lem4803639 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term335 _110698 x s x' y) = (term336 _110698 x s x' y).
Proof. exact (@lem19699 (term22 _110698 x' x) (term331 _110698 x' s) (term135 _110698 s x' y)). Qed.
Lemma lem4803646 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (x' : _110698) (y : _110698) : (term337 _110698 s x x' y) = (term338 _110698 s x x' y).
Proof. exact (@lem19699 (term22 _110698 x' x) (term331 _110698 x' s) (term334 _110698 x x' y)). Qed.
Lemma lem4803647 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4803648 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (x' : _110698) (y : _110698) : (term339 _110698 s x x' y) = (term340 _110698 s x x' y).
Proof. exact (MK_COMB (@lem4803647) (@lem4803646 _110698 s x x' y)). Qed.
Lemma lem4803649 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term333 _110698 x s x' y) = (term341 _110698 x s x' y).
Proof. exact (MK_COMB (@lem4803648 _110698 s x x' y) (@lem4803639 _110698 x s x' y)). Qed.
Lemma lem4803650 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term332 _110698 x s x' y) = (term341 _110698 x s x' y).
Proof. exact (TRANS (@lem4803632 _110698 x s x' y) (@lem4803649 _110698 x s x' y)). Qed.
Lemma lem4803651 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term81 _110698 x s x' y) = (term341 _110698 x s x' y).
Proof. exact (TRANS (@lem4803631 _110698 x s x' y) (@lem4803650 _110698 x s x' y)). Qed.
Lemma lem4803652 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4803653 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term86 _110698 x s x' y) = (term342 _110698 x s x' y).
Proof. exact (MK_COMB (@lem4803652) (@lem4803651 _110698 x s x' y)). Qed.
Lemma lem4803654 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term88 _110698 x s r x' y) = (term343 _110698 x s r x' y).
Proof. exact (MK_COMB (@lem4803653 _110698 x s x' y) (@lem4803606 _110698 r x' y)). Qed.
Lemma lem4803655 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term343 _110698 x s r x' y) = (term344 _110698 x s r x' y).
Proof. exact (@lem19699 (term338 _110698 s x x' y) (term336 _110698 x s x' y) (r x' y)). Qed.
Lemma lem4803662 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term345 _110698 x s r x' y) = (term346 _110698 x s r x' y).
Proof. exact (@lem19699 (term347 _110698 x s x' y) (term138 _110698 s x' y) (r x' y)). Qed.
Lemma lem4803669 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term348 _110698 s x r x' y) = (term349 _110698 s x r x' y).
Proof. exact (@lem19699 (term350 _110698 x x' y) (term351 _110698 s x x' y) (r x' y)). Qed.
Lemma lem4803670 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4803671 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term352 _110698 s x r x' y) = (term353 _110698 s x r x' y).
Proof. exact (MK_COMB (@lem4803670) (@lem4803669 _110698 s x r x' y)). Qed.
Lemma lem4803672 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term344 _110698 x s r x' y) = (term354 _110698 x s r x' y).
Proof. exact (MK_COMB (@lem4803671 _110698 s x r x' y) (@lem4803662 _110698 x s r x' y)). Qed.
Lemma lem4803673 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term343 _110698 x s r x' y) = (term354 _110698 x s r x' y).
Proof. exact (TRANS (@lem4803655 _110698 x s r x' y) (@lem4803672 _110698 x s r x' y)). Qed.
Lemma lem4803674 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term88 _110698 x s r x' y) = (term354 _110698 x s r x' y).
Proof. exact (TRANS (@lem4803654 _110698 x s r x' y) (@lem4803673 _110698 x s r x' y)). Qed.
Lemma lem4803675 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term98 _110698 x s r x') = (term355 _110698 x s r x').
Proof. exact (fun_ext (fun y : _110698 => @lem4803674 _110698 x s r x' y)). Qed.
Lemma lem4803676 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4803677 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term99 _110698 x s r x') = (term356 _110698 x s r x').
Proof. exact (MK_COMB (@lem4803676 _110698) (@lem4803675 _110698 x s r x')). Qed.
Lemma lem4803678 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term107 _110698 x s r) = (term357 _110698 x s r).
Proof. exact (fun_ext (fun x' : _110698 => @lem4803677 _110698 x s r x')). Qed.
Lemma lem4803679 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4803681 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term108 _110698 x s r) = (term358 _110698 x s r).
Proof. exact (MK_COMB (@lem4803679 _110698) (@lem4803678 _110698 x s r)). Qed.
Lemma lem4803682 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term358 _110698 x s r.
Proof. exact (EQ_MP (@lem4803681 _110698 x s r) (@lem4803484 _110698 x s r y y' h1)). Qed.
Lemma lem4803694 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term359 _110698 r y x) : term359 _110698 r y x.
Proof. exact (h1). Qed.
Lemma lem4803696 {_110698 : Type'} (r : type1402 _110698) (x' : _110698) (y : _110698) : (r x' y) = (r x' y).
Proof. exact (eq_refl (r x' y)). Qed.
Lemma lem4803713 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term78 _110698 x s x' y) = (term330 _110698 x s x' y).
Proof. exact (@lem19699 (term22 _110698 y x) (term331 _110698 y s) (x' = y)). Qed.
Lemma lem4803720 {_110698 : Type'} (x : _110698) (x' : _110698) (s : _110698 -> Prop) : (term76 _110698 x x' s) = (term76 _110698 x x' s).
Proof. exact (eq_refl (term76 _110698 x x' s)). Qed.
Lemma lem4803721 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term81 _110698 x s x' y) = (term332 _110698 x s x' y).
Proof. exact (MK_COMB (@lem4803720 _110698 x x' s) (@lem4803713 _110698 x s x' y)). Qed.
Lemma lem4803722 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term332 _110698 x s x' y) = (term333 _110698 x s x' y).
Proof. exact (@lem19490 (term334 _110698 x x' y) (term73 _110698 x x' s) (term135 _110698 s x' y)). Qed.
Lemma lem4803729 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term335 _110698 x s x' y) = (term336 _110698 x s x' y).
Proof. exact (@lem19699 (term22 _110698 x' x) (term331 _110698 x' s) (term135 _110698 s x' y)). Qed.
Lemma lem4803736 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (x' : _110698) (y : _110698) : (term337 _110698 s x x' y) = (term338 _110698 s x x' y).
Proof. exact (@lem19699 (term22 _110698 x' x) (term331 _110698 x' s) (term334 _110698 x x' y)). Qed.
Lemma lem4803737 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4803738 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (x' : _110698) (y : _110698) : (term339 _110698 s x x' y) = (term340 _110698 s x x' y).
Proof. exact (MK_COMB (@lem4803737) (@lem4803736 _110698 s x x' y)). Qed.
Lemma lem4803739 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term333 _110698 x s x' y) = (term341 _110698 x s x' y).
Proof. exact (MK_COMB (@lem4803738 _110698 s x x' y) (@lem4803729 _110698 x s x' y)). Qed.
Lemma lem4803740 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term332 _110698 x s x' y) = (term341 _110698 x s x' y).
Proof. exact (TRANS (@lem4803722 _110698 x s x' y) (@lem4803739 _110698 x s x' y)). Qed.
Lemma lem4803741 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term81 _110698 x s x' y) = (term341 _110698 x s x' y).
Proof. exact (TRANS (@lem4803721 _110698 x s x' y) (@lem4803740 _110698 x s x' y)). Qed.
Lemma lem4803742 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4803743 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (x' : _110698) (y : _110698) : (term86 _110698 x s x' y) = (term342 _110698 x s x' y).
Proof. exact (MK_COMB (@lem4803742) (@lem4803741 _110698 x s x' y)). Qed.
Lemma lem4803744 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term88 _110698 x s r x' y) = (term343 _110698 x s r x' y).
Proof. exact (MK_COMB (@lem4803743 _110698 x s x' y) (@lem4803696 _110698 r x' y)). Qed.
Lemma lem4803745 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term343 _110698 x s r x' y) = (term344 _110698 x s r x' y).
Proof. exact (@lem19699 (term338 _110698 s x x' y) (term336 _110698 x s x' y) (r x' y)). Qed.
Lemma lem4803752 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term345 _110698 x s r x' y) = (term346 _110698 x s r x' y).
Proof. exact (@lem19699 (term347 _110698 x s x' y) (term138 _110698 s x' y) (r x' y)). Qed.
Lemma lem4803759 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term348 _110698 s x r x' y) = (term349 _110698 s x r x' y).
Proof. exact (@lem19699 (term350 _110698 x x' y) (term351 _110698 s x x' y) (r x' y)). Qed.
Lemma lem4803760 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4803761 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term352 _110698 s x r x' y) = (term353 _110698 s x r x' y).
Proof. exact (MK_COMB (@lem4803760) (@lem4803759 _110698 s x r x' y)). Qed.
Lemma lem4803762 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term344 _110698 x s r x' y) = (term354 _110698 x s r x' y).
Proof. exact (MK_COMB (@lem4803761 _110698 s x r x' y) (@lem4803752 _110698 x s r x' y)). Qed.
Lemma lem4803763 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term343 _110698 x s r x' y) = (term354 _110698 x s r x' y).
Proof. exact (TRANS (@lem4803745 _110698 x s r x' y) (@lem4803762 _110698 x s r x' y)). Qed.
Lemma lem4803764 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) (y : _110698) : (term88 _110698 x s r x' y) = (term354 _110698 x s r x' y).
Proof. exact (TRANS (@lem4803744 _110698 x s r x' y) (@lem4803763 _110698 x s r x' y)). Qed.
Lemma lem4803765 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term98 _110698 x s r x') = (term355 _110698 x s r x').
Proof. exact (fun_ext (fun y : _110698 => @lem4803764 _110698 x s r x' y)). Qed.
Lemma lem4803766 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4803767 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (x' : _110698) : (term99 _110698 x s r x') = (term356 _110698 x s r x').
Proof. exact (MK_COMB (@lem4803766 _110698) (@lem4803765 _110698 x s r x')). Qed.
Lemma lem4803768 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term107 _110698 x s r) = (term357 _110698 x s r).
Proof. exact (fun_ext (fun x' : _110698 => @lem4803767 _110698 x s r x')). Qed.
Lemma lem4803769 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4803771 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term108 _110698 x s r) = (term358 _110698 x s r).
Proof. exact (MK_COMB (@lem4803769 _110698) (@lem4803768 _110698 x s r)). Qed.
Lemma lem4803772 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term358 _110698 x s r.
Proof. exact (EQ_MP (@lem4803771 _110698 x s r) (@lem4803484 _110698 x s r y y' h1)). Qed.
Lemma lem4803857 {_110698 : Type'} (y' : _110698) (x : _110698) (h1 : y' = x) : y' = x.
Proof. exact (h1). Qed.
Lemma lem4803861 {_110698 : Type'} (y : _110698) (x : _110698) (h1 : y = x) : y = x.
Proof. exact (h1). Qed.
Lemma lem4803885 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) : (term124 _110698 s r y x) = (term360 _110698 s r y x).
Proof. exact (@lem19490 (r x y) (term111 _110698 s y x) (r y x)). Qed.
Lemma lem4803886 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term132 _110698 s r x) = (term361 _110698 s r x).
Proof. exact (fun_ext (fun y : _110698 => @lem4803885 _110698 s r y x)). Qed.
Lemma lem4803887 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4803889 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term133 _110698 s r x) = (term362 _110698 s r x).
Proof. exact (MK_COMB (@lem4803887 _110698) (@lem4803886 _110698 s r x)). Qed.
Lemma lem4803890 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term362 _110698 s r x.
Proof. exact (EQ_MP (@lem4803889 _110698 s r x) (@lem4803502 _110698 y y' x s r h1)). Qed.
Lemma lem4803930 {_110698 : Type'} (y' : _110698) (x : _110698) (h1 : y' = x) : y' = x.
Proof. exact (h1). Qed.
Lemma lem4803934 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) (h1 : @IN _110698 y s) : @IN _110698 y s.
Proof. exact (h1). Qed.
Lemma lem4803958 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) : (term124 _110698 s r y x) = (term360 _110698 s r y x).
Proof. exact (@lem19490 (r x y) (term111 _110698 s y x) (r y x)). Qed.
Lemma lem4803959 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term132 _110698 s r x) = (term361 _110698 s r x).
Proof. exact (fun_ext (fun y : _110698 => @lem4803958 _110698 s r y x)). Qed.
Lemma lem4803960 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4803962 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term133 _110698 s r x) = (term362 _110698 s r x).
Proof. exact (MK_COMB (@lem4803960 _110698) (@lem4803959 _110698 s r x)). Qed.
Lemma lem4803963 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term362 _110698 s r x.
Proof. exact (EQ_MP (@lem4803962 _110698 s r x) (@lem4803502 _110698 y y' x s r h1)). Qed.
Lemma lem4804003 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (h1 : @IN _110698 y' s) : @IN _110698 y' s.
Proof. exact (h1). Qed.
Lemma lem4804007 {_110698 : Type'} (y : _110698) (x : _110698) (h1 : y = x) : y = x.
Proof. exact (h1). Qed.
Lemma lem4804056 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) (y : _110698) : (term147 _110698 s r x y) = (term147 _110698 s r x y).
Proof. exact (eq_refl (term147 _110698 s r x y)). Qed.
Lemma lem4804057 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term155 _110698 s r x) = (term155 _110698 s r x).
Proof. exact (fun_ext (fun y : _110698 => @lem4804056 _110698 s r x y)). Qed.
Lemma lem4804058 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4804059 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) : (term156 _110698 s r x) = (term156 _110698 s r x).
Proof. exact (MK_COMB (@lem4804058 _110698) (@lem4804057 _110698 s r x)). Qed.
Lemma lem4804060 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) : (term164 _110698 s r) = (term164 _110698 s r).
Proof. exact (fun_ext (fun x : _110698 => @lem4804059 _110698 s r x)). Qed.
Lemma lem4804061 {_110698 : Type'} : (@all _110698) = (@all _110698).
Proof. exact (eq_refl (@all _110698)). Qed.
Lemma lem4804063 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) : (term165 _110698 s r) = (term165 _110698 s r).
Proof. exact (MK_COMB (@lem4804061 _110698) (@lem4804060 _110698 s r)). Qed.
Lemma lem4804064 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term165 _110698 s r.
Proof. exact (EQ_MP (@lem4804063 _110698 s r) (@lem4803501 _110698 y y' x s r h1)). Qed.
Lemma lem4804076 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (h1 : @IN _110698 y' s) : @IN _110698 y' s.
Proof. exact (h1). Qed.
Lemma lem4804080 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) (h1 : @IN _110698 y s) : @IN _110698 y s.
Proof. exact (h1). Qed.
Lemma lem4804081 {_110698 : Type'} (_59430 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term363 _110698 x s r _59430.
Proof. exact (@lem4803592 _110698 x s r y y' h1 _59430). Qed.
Lemma lem4804082 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (_59430 : _110698) : (term363 _110698 x s r _59430) = (term356 _110698 x s r _59430).
Proof. exact (eq_refl (term363 _110698 x s r _59430)). Qed.
Lemma lem4804083 {_110698 : Type'} (_59430 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term356 _110698 x s r _59430.
Proof. exact (EQ_MP (@lem4804082 _110698 x s r _59430) (@lem4804081 _110698 _59430 x s r y y' h1)). Qed.
Lemma lem4804084 {_110698 : Type'} (_59430 : _110698) (_59431 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term364 _110698 x s r _59430 _59431.
Proof. exact (@lem4804083 _110698 _59430 x s r y y' h1 _59431). Qed.
Lemma lem4804085 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (_59430 : _110698) (_59431 : _110698) : (term364 _110698 x s r _59430 _59431) = (term354 _110698 x s r _59430 _59431).
Proof. exact (eq_refl (term364 _110698 x s r _59430 _59431)). Qed.
Lemma lem4804086 {_110698 : Type'} (_59430 : _110698) (_59431 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term354 _110698 x s r _59430 _59431.
Proof. exact (EQ_MP (@lem4804085 _110698 x s r _59430 _59431) (@lem4804084 _110698 _59430 _59431 x s r y y' h1)). Qed.
Lemma lem4804087 {_110698 : Type'} (_59432 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term363 _110698 x s r _59432.
Proof. exact (@lem4803682 _110698 x s r y y' h1 _59432). Qed.
Lemma lem4804088 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (_59432 : _110698) : (term363 _110698 x s r _59432) = (term356 _110698 x s r _59432).
Proof. exact (eq_refl (term363 _110698 x s r _59432)). Qed.
Lemma lem4804089 {_110698 : Type'} (_59432 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term356 _110698 x s r _59432.
Proof. exact (EQ_MP (@lem4804088 _110698 x s r _59432) (@lem4804087 _110698 _59432 x s r y y' h1)). Qed.
Lemma lem4804090 {_110698 : Type'} (_59432 : _110698) (_59433 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term364 _110698 x s r _59432 _59433.
Proof. exact (@lem4804089 _110698 _59432 x s r y y' h1 _59433). Qed.
Lemma lem4804091 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (_59432 : _110698) (_59433 : _110698) : (term364 _110698 x s r _59432 _59433) = (term354 _110698 x s r _59432 _59433).
Proof. exact (eq_refl (term364 _110698 x s r _59432 _59433)). Qed.
Lemma lem4804092 {_110698 : Type'} (_59432 : _110698) (_59433 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term354 _110698 x s r _59432 _59433.
Proof. exact (EQ_MP (@lem4804091 _110698 x s r _59432 _59433) (@lem4804090 _110698 _59432 _59433 x s r y y' h1)). Qed.
Lemma lem4804093 {_110698 : Type'} (_59434 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term363 _110698 x s r _59434.
Proof. exact (@lem4803772 _110698 x s r y y' h1 _59434). Qed.
Lemma lem4804094 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (_59434 : _110698) : (term363 _110698 x s r _59434) = (term356 _110698 x s r _59434).
Proof. exact (eq_refl (term363 _110698 x s r _59434)). Qed.
Lemma lem4804095 {_110698 : Type'} (_59434 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term356 _110698 x s r _59434.
Proof. exact (EQ_MP (@lem4804094 _110698 x s r _59434) (@lem4804093 _110698 _59434 x s r y y' h1)). Qed.
Lemma lem4804096 {_110698 : Type'} (_59434 : _110698) (_59435 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term364 _110698 x s r _59434 _59435.
Proof. exact (@lem4804095 _110698 _59434 x s r y y' h1 _59435). Qed.
Lemma lem4804097 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) : (term364 _110698 x s r _59434 _59435) = (term354 _110698 x s r _59434 _59435).
Proof. exact (eq_refl (term364 _110698 x s r _59434 _59435)). Qed.
Lemma lem4804098 {_110698 : Type'} (_59434 : _110698) (_59435 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term354 _110698 x s r _59434 _59435.
Proof. exact (EQ_MP (@lem4804097 _110698 x s r _59434 _59435) (@lem4804096 _110698 _59434 _59435 x s r y y' h1)). Qed.
Lemma lem4804108 {_110698 : Type'} (_59439 : _110698) (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term365 _110698 s r x _59439.
Proof. exact (@lem4803890 _110698 y y' x s r h1 _59439). Qed.
Lemma lem4804109 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59439 : _110698) (x : _110698) : (term365 _110698 s r x _59439) = (term360 _110698 s r _59439 x).
Proof. exact (eq_refl (term365 _110698 s r x _59439)). Qed.
Lemma lem4804110 {_110698 : Type'} (_59439 : _110698) (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term360 _110698 s r _59439 x.
Proof. exact (EQ_MP (@lem4804109 _110698 s r _59439 x) (@lem4804108 _110698 _59439 y y' x s r h1)). Qed.
Lemma lem4804117 {_110698 : Type'} (_59442 : _110698) (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term365 _110698 s r x _59442.
Proof. exact (@lem4803963 _110698 y y' x s r h1 _59442). Qed.
Lemma lem4804118 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59442 : _110698) (x : _110698) : (term365 _110698 s r x _59442) = (term360 _110698 s r _59442 x).
Proof. exact (eq_refl (term365 _110698 s r x _59442)). Qed.
Lemma lem4804119 {_110698 : Type'} (_59442 : _110698) (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term360 _110698 s r _59442 x.
Proof. exact (EQ_MP (@lem4804118 _110698 s r _59442 x) (@lem4804117 _110698 _59442 y y' x s r h1)). Qed.
Lemma lem4804129 {_110698 : Type'} (_59446 : _110698) (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term366 _110698 s r _59446.
Proof. exact (@lem4804064 _110698 y y' x s r h1 _59446). Qed.
Lemma lem4804130 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59446 : _110698) : (term366 _110698 s r _59446) = (term156 _110698 s r _59446).
Proof. exact (eq_refl (term366 _110698 s r _59446)). Qed.
Lemma lem4804131 {_110698 : Type'} (_59446 : _110698) (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term156 _110698 s r _59446.
Proof. exact (EQ_MP (@lem4804130 _110698 s r _59446) (@lem4804129 _110698 _59446 y y' x s r h1)). Qed.
Lemma lem4804132 {_110698 : Type'} (_59446 : _110698) (_59447 : _110698) (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term367 _110698 s r _59446 _59447.
Proof. exact (@lem4804131 _110698 _59446 y y' x s r h1 _59447). Qed.
Lemma lem4804133 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) : (term367 _110698 s r _59446 _59447) = (term147 _110698 s r _59446 _59447).
Proof. exact (eq_refl (term367 _110698 s r _59446 _59447)). Qed.
Lemma lem4804134 {_110698 : Type'} (_59446 : _110698) (_59447 : _110698) (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term147 _110698 s r _59446 _59447.
Proof. exact (EQ_MP (@lem4804133 _110698 s r _59446 _59447) (@lem4804132 _110698 _59446 _59447 y y' x s r h1)). Qed.
Lemma lem4804135 {_110698 : Type'} (_59430 : _110698) (_59431 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term346 _110698 x s r _59430 _59431.
Proof. exact (proj2 (@lem4804086 _110698 _59430 _59431 x s r y y' h1)). Qed.
Lemma lem4804138 {_110698 : Type'} (_59430 : _110698) (_59431 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term368 _110698 x s r _59430 _59431.
Proof. exact (proj1 (@lem4804135 _110698 _59430 _59431 x s r y y' h1)). Qed.
Lemma lem4804142 {_110698 : Type'} (_59432 : _110698) (_59433 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term349 _110698 s x r _59432 _59433.
Proof. exact (proj1 (@lem4804092 _110698 _59432 _59433 x s r y y' h1)). Qed.
Lemma lem4804145 {_110698 : Type'} (_59432 : _110698) (_59433 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term369 _110698 s x r _59432 _59433.
Proof. exact (proj2 (@lem4804142 _110698 _59432 _59433 x s r y y' h1)). Qed.
Lemma lem4804147 {_110698 : Type'} (_59434 : _110698) (_59435 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term346 _110698 x s r _59434 _59435.
Proof. exact (proj2 (@lem4804098 _110698 _59434 _59435 x s r y y' h1)). Qed.
Lemma lem4804149 {_110698 : Type'} (_59434 : _110698) (_59435 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term147 _110698 s r _59434 _59435.
Proof. exact (proj2 (@lem4804147 _110698 _59434 _59435 x s r y y' h1)). Qed.
Lemma lem4804155 {_110698 : Type'} (_59439 : _110698) (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term370 _110698 s r _59439 x.
Proof. exact (proj2 (@lem4804110 _110698 _59439 y y' x s r h1)). Qed.
Lemma lem4804158 {_110698 : Type'} (_59442 : _110698) (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term371 _110698 s r x _59442.
Proof. exact (proj1 (@lem4804119 _110698 _59442 y y' x s r h1)). Qed.
Lemma lem4804166 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (y : _110698) (h1 : term359 _110698 r x y) : term359 _110698 r x y.
Proof. exact (h1). Qed.
Lemma lem4804170 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (_59430 : _110698) (_59431 : _110698) : (term368 _110698 x s r _59430 _59431) = (term372 _110698 x s r _59430 _59431).
Proof. exact (@lem4802040 (term22 _110698 _59430 x) (term135 _110698 s _59430 _59431) (r _59430 _59431)). Qed.
Lemma lem4804177 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59430 : _110698) (_59431 : _110698) : (term373 _110698 s r _59430 _59431) = (term374 _110698 s r _59430 _59431).
Proof. exact (@lem4802040 (term331 _110698 _59431 s) (_59430 = _59431) (r _59430 _59431)). Qed.
Lemma lem4804178 {_110698 : Type'} (_59430 : _110698) (x : _110698) : (term375 _110698 _59430 x) = (term375 _110698 _59430 x).
Proof. exact (eq_refl (term375 _110698 _59430 x)). Qed.
Lemma lem4804181 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (_59430 : _110698) (_59431 : _110698) : (term372 _110698 x s r _59430 _59431) = (term376 _110698 x s r _59430 _59431).
Proof. exact (MK_COMB (@lem4804178 _110698 _59430 x) (@lem4804177 _110698 s r _59430 _59431)). Qed.
Lemma lem4804183 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (_59430 : _110698) (_59431 : _110698) : (term368 _110698 x s r _59430 _59431) = (term376 _110698 x s r _59430 _59431).
Proof. exact (TRANS (@lem4804170 _110698 x s r _59430 _59431) (@lem4804181 _110698 x s r _59430 _59431)). Qed.
Lemma lem4804184 {_110698 : Type'} (_59430 : _110698) (_59431 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term376 _110698 x s r _59430 _59431.
Proof. exact (EQ_MP (@lem4804183 _110698 x s r _59430 _59431) (@lem4804138 _110698 _59430 _59431 x s r y y' h1)). Qed.
Lemma lem4804244 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term359 _110698 r y x) : term359 _110698 r y x.
Proof. exact (h1). Qed.
Lemma lem4804302 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (r : type1402 _110698) (_59432 : _110698) (_59433 : _110698) : (term369 _110698 s x r _59432 _59433) = (term377 _110698 s x r _59432 _59433).
Proof. exact (@lem4802040 (term331 _110698 _59432 s) (term334 _110698 x _59432 _59433) (r _59432 _59433)). Qed.
Lemma lem4804309 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (_59432 : _110698) (_59433 : _110698) : (term378 _110698 x r _59432 _59433) = (term379 _110698 x r _59432 _59433).
Proof. exact (@lem4802040 (term22 _110698 _59433 x) (_59432 = _59433) (r _59432 _59433)). Qed.
Lemma lem4804310 {_110698 : Type'} (_59432 : _110698) (s : _110698 -> Prop) : (term109 _110698 _59432 s) = (term109 _110698 _59432 s).
Proof. exact (eq_refl (term109 _110698 _59432 s)). Qed.
Lemma lem4804313 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (r : type1402 _110698) (_59432 : _110698) (_59433 : _110698) : (term377 _110698 s x r _59432 _59433) = (term380 _110698 s x r _59432 _59433).
Proof. exact (MK_COMB (@lem4804310 _110698 _59432 s) (@lem4804309 _110698 x r _59432 _59433)). Qed.
Lemma lem4804315 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (r : type1402 _110698) (_59432 : _110698) (_59433 : _110698) : (term369 _110698 s x r _59432 _59433) = (term380 _110698 s x r _59432 _59433).
Proof. exact (TRANS (@lem4804302 _110698 s x r _59432 _59433) (@lem4804313 _110698 s x r _59432 _59433)). Qed.
Lemma lem4804316 {_110698 : Type'} (_59432 : _110698) (_59433 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term380 _110698 s x r _59432 _59433.
Proof. exact (EQ_MP (@lem4804315 _110698 s x r _59432 _59433) (@lem4804145 _110698 _59432 _59433 x s r y y' h1)). Qed.
Lemma lem4804324 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term142 _110698 s r y y') : term22 _110698 y y'.
Proof. exact (proj2 (@lem4803495 _110698 s r y y' h1)). Qed.
Lemma lem4804346 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) : (term147 _110698 s r _59434 _59435) = (term381 _110698 s r _59434 _59435).
Proof. exact (@lem4802040 (term331 _110698 _59434 s) (term135 _110698 s _59434 _59435) (r _59434 _59435)). Qed.
Lemma lem4804353 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) : (term373 _110698 s r _59434 _59435) = (term374 _110698 s r _59434 _59435).
Proof. exact (@lem4802040 (term331 _110698 _59435 s) (_59434 = _59435) (r _59434 _59435)). Qed.
Lemma lem4804354 {_110698 : Type'} (_59434 : _110698) (s : _110698 -> Prop) : (term109 _110698 _59434 s) = (term109 _110698 _59434 s).
Proof. exact (eq_refl (term109 _110698 _59434 s)). Qed.
Lemma lem4804357 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) : (term381 _110698 s r _59434 _59435) = (term382 _110698 s r _59434 _59435).
Proof. exact (MK_COMB (@lem4804354 _110698 _59434 s) (@lem4804353 _110698 s r _59434 _59435)). Qed.
Lemma lem4804359 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) : (term147 _110698 s r _59434 _59435) = (term382 _110698 s r _59434 _59435).
Proof. exact (TRANS (@lem4804346 _110698 s r _59434 _59435) (@lem4804357 _110698 s r _59434 _59435)). Qed.
Lemma lem4804360 {_110698 : Type'} (_59434 : _110698) (_59435 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term382 _110698 s r _59434 _59435.
Proof. exact (EQ_MP (@lem4804359 _110698 s r _59434 _59435) (@lem4804149 _110698 _59434 _59435 x s r y y' h1)). Qed.
Lemma lem4804418 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term22 _110698 y y'.
Proof. exact (proj2 (@lem4803505 _110698 y y' x s r h1)). Qed.
Lemma lem4804420 {_110698 : Type'} (y' : _110698) (x : _110698) (h1 : y' = x) : y' = x.
Proof. exact (h1). Qed.
Lemma lem4804422 {_110698 : Type'} (y : _110698) (x : _110698) (h1 : y = x) : y = x.
Proof. exact (h1). Qed.
Lemma lem4804466 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term359 _110698 r y y'.
Proof. exact (proj2 (@lem4803500 _110698 y y' x s r h1)). Qed.
Lemma lem4804468 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term22 _110698 y y'.
Proof. exact (proj2 (@lem4803505 _110698 y y' x s r h1)). Qed.
Lemma lem4804470 {_110698 : Type'} (y' : _110698) (x : _110698) (h1 : y' = x) : y' = x.
Proof. exact (h1). Qed.
Lemma lem4804472 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) (h1 : @IN _110698 y s) : @IN _110698 y s.
Proof. exact (h1). Qed.
Lemma lem4804495 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59439 : _110698) (x : _110698) : (term370 _110698 s r _59439 x) = (term383 _110698 s r _59439 x).
Proof. exact (@lem4802040 (term331 _110698 _59439 s) (_59439 = x) (r _59439 x)). Qed.
Lemma lem4804516 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term359 _110698 r y y'.
Proof. exact (proj2 (@lem4803500 _110698 y y' x s r h1)). Qed.
Lemma lem4804518 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term22 _110698 y y'.
Proof. exact (proj2 (@lem4803505 _110698 y y' x s r h1)). Qed.
Lemma lem4804520 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (h1 : @IN _110698 y' s) : @IN _110698 y' s.
Proof. exact (h1). Qed.
Lemma lem4804522 {_110698 : Type'} (y : _110698) (x : _110698) (h1 : y = x) : y = x.
Proof. exact (h1). Qed.
Lemma lem4804533 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) (_59442 : _110698) : (term371 _110698 s r x _59442) = (term384 _110698 s r x _59442).
Proof. exact (@lem4802040 (term331 _110698 _59442 s) (_59442 = x) (r x _59442)). Qed.
Lemma lem4804550 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) : (term147 _110698 s r _59446 _59447) = (term381 _110698 s r _59446 _59447).
Proof. exact (@lem4802040 (term331 _110698 _59446 s) (term135 _110698 s _59446 _59447) (r _59446 _59447)). Qed.
Lemma lem4804557 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) : (term373 _110698 s r _59446 _59447) = (term374 _110698 s r _59446 _59447).
Proof. exact (@lem4802040 (term331 _110698 _59447 s) (_59446 = _59447) (r _59446 _59447)). Qed.
Lemma lem4804558 {_110698 : Type'} (_59446 : _110698) (s : _110698 -> Prop) : (term109 _110698 _59446 s) = (term109 _110698 _59446 s).
Proof. exact (eq_refl (term109 _110698 _59446 s)). Qed.
Lemma lem4804561 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) : (term381 _110698 s r _59446 _59447) = (term382 _110698 s r _59446 _59447).
Proof. exact (MK_COMB (@lem4804558 _110698 _59446 s) (@lem4804557 _110698 s r _59446 _59447)). Qed.
Lemma lem4804563 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) : (term147 _110698 s r _59446 _59447) = (term382 _110698 s r _59446 _59447).
Proof. exact (TRANS (@lem4804550 _110698 s r _59446 _59447) (@lem4804561 _110698 s r _59446 _59447)). Qed.
Lemma lem4804564 {_110698 : Type'} (_59446 : _110698) (_59447 : _110698) (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term382 _110698 s r _59446 _59447.
Proof. exact (EQ_MP (@lem4804563 _110698 s r _59446 _59447) (@lem4804134 _110698 _59446 _59447 y y' x s r h1)). Qed.
Lemma lem4804568 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term22 _110698 y y'.
Proof. exact (proj2 (@lem4803505 _110698 y y' x s r h1)). Qed.
Lemma lem4804570 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (h1 : @IN _110698 y' s) : @IN _110698 y' s.
Proof. exact (h1). Qed.
Lemma lem4804572 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) (h1 : @IN _110698 y s) : @IN _110698 y s.
Proof. exact (h1). Qed.
Lemma lem4804638 {_110698 : Type'} (y' : _110698) : (term385 _110698 y') = (term385 _110698 y').
Proof. exact (eq_refl (term385 _110698 y')). Qed.
Lemma lem4804639 {_110698 : Type'} (y' : _110698) (y : _110698) (x : _110698) (h1 : y = x) : (term386 _110698 y' y) = (term386 _110698 y' x).
Proof. exact (MK_COMB (@lem4804638 _110698 y') (@lem4804422 _110698 y x h1)). Qed.
Lemma lem4804640 {_110698 : Type'} (x : _110698) (y' : _110698) : (term386 _110698 y' x) = (term22 _110698 x y').
Proof. exact (eq_refl (term386 _110698 y' x)). Qed.
Lemma lem4804641 {_110698 : Type'} (y' : _110698) (y : _110698) : (term387 _110698 y' y) = (term387 _110698 y' y).
Proof. exact (eq_refl (term387 _110698 y' y)). Qed.
Lemma lem4804642 {_110698 : Type'} (y : _110698) (x : _110698) (y' : _110698) : ((term386 _110698 y' y) = (term386 _110698 y' x)) = ((term386 _110698 y' y) = (term22 _110698 x y')).
Proof. exact (MK_COMB (@lem4804641 _110698 y' y) (@lem4804640 _110698 x y')). Qed.
Lemma lem4804643 {_110698 : Type'} (y : _110698) (y' : _110698) : (term386 _110698 y' y) = (term22 _110698 y y').
Proof. exact (eq_refl (term386 _110698 y' y)). Qed.
Lemma lem4804644 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4804645 {_110698 : Type'} (y : _110698) (y' : _110698) : (term387 _110698 y' y) = (term388 _110698 y y').
Proof. exact (MK_COMB (@lem4804644) (@lem4804643 _110698 y y')). Qed.
Lemma lem4804646 {_110698 : Type'} (x : _110698) (y' : _110698) : (term22 _110698 x y') = (term22 _110698 x y').
Proof. exact (eq_refl (term22 _110698 x y')). Qed.
Lemma lem4804647 {_110698 : Type'} (y : _110698) (x : _110698) (y' : _110698) : ((term386 _110698 y' y) = (term22 _110698 x y')) = ((term22 _110698 y y') = (term22 _110698 x y')).
Proof. exact (MK_COMB (@lem4804645 _110698 y y') (@lem4804646 _110698 x y')). Qed.
Lemma lem4804648 {_110698 : Type'} (y : _110698) (x : _110698) (y' : _110698) : ((term386 _110698 y' y) = (term386 _110698 y' x)) = ((term22 _110698 y y') = (term22 _110698 x y')).
Proof. exact (TRANS (@lem4804642 _110698 y x y') (@lem4804647 _110698 y x y')). Qed.
Lemma lem4804649 {_110698 : Type'} (y' : _110698) (y : _110698) (x : _110698) (h1 : y = x) : (term22 _110698 y y') = (term22 _110698 x y').
Proof. exact (EQ_MP (@lem4804648 _110698 y x y') (@lem4804639 _110698 y' y x h1)). Qed.
Lemma lem4804650 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) : term22 _110698 x y'.
Proof. exact (EQ_MP (@lem4804649 _110698 y' y x h2) (@lem4804418 _110698 y y' x s r h1)). Qed.
Lemma lem4804664 {_110698 : Type'} (y' : _110698) (x : _110698) (h1 : y' = x) : y' = x.
Proof. exact (h1). Qed.
Lemma lem4804734 {_110698 : Type'} (x : _110698) : (term389 _110698 x) = (term389 _110698 x).
Proof. exact (eq_refl (term389 _110698 x)). Qed.
Lemma lem4804735 {_110698 : Type'} (y' : _110698) (x : _110698) (h1 : y' = x) : (term390 _110698 x y') = (term391 _110698 x).
Proof. exact (MK_COMB (@lem4804734 _110698 x) (@lem4804664 _110698 y' x h1)). Qed.
Lemma lem4804736 {_110698 : Type'} (x : _110698) : (term391 _110698 x) = (term392 _110698 x).
Proof. exact (eq_refl (term391 _110698 x)). Qed.
Lemma lem4804737 {_110698 : Type'} (x : _110698) (y' : _110698) : (term393 _110698 x y') = (term393 _110698 x y').
Proof. exact (eq_refl (term393 _110698 x y')). Qed.
Lemma lem4804738 {_110698 : Type'} (y' : _110698) (x : _110698) : ((term390 _110698 x y') = (term391 _110698 x)) = ((term390 _110698 x y') = (term392 _110698 x)).
Proof. exact (MK_COMB (@lem4804737 _110698 x y') (@lem4804736 _110698 x)). Qed.
Lemma lem4804739 {_110698 : Type'} (x : _110698) (y' : _110698) : (term390 _110698 x y') = (term22 _110698 x y').
Proof. exact (eq_refl (term390 _110698 x y')). Qed.
Lemma lem4804740 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4804741 {_110698 : Type'} (x : _110698) (y' : _110698) : (term393 _110698 x y') = (term388 _110698 x y').
Proof. exact (MK_COMB (@lem4804740) (@lem4804739 _110698 x y')). Qed.
Lemma lem4804742 {_110698 : Type'} (x : _110698) : (term392 _110698 x) = (term392 _110698 x).
Proof. exact (eq_refl (term392 _110698 x)). Qed.
Lemma lem4804743 {_110698 : Type'} (y' : _110698) (x : _110698) : ((term390 _110698 x y') = (term392 _110698 x)) = ((term22 _110698 x y') = (term392 _110698 x)).
Proof. exact (MK_COMB (@lem4804741 _110698 x y') (@lem4804742 _110698 x)). Qed.
Lemma lem4804744 {_110698 : Type'} (y' : _110698) (x : _110698) : ((term390 _110698 x y') = (term391 _110698 x)) = ((term22 _110698 x y') = (term392 _110698 x)).
Proof. exact (TRANS (@lem4804738 _110698 y' x) (@lem4804743 _110698 y' x)). Qed.
Lemma lem4804745 {_110698 : Type'} (y' : _110698) (x : _110698) (h1 : y' = x) : (term22 _110698 x y') = (term392 _110698 x).
Proof. exact (EQ_MP (@lem4804744 _110698 y' x) (@lem4804735 _110698 y' x h1)). Qed.
Lemma lem4804746 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : y' = x) : term392 _110698 x.
Proof. exact (EQ_MP (@lem4804745 _110698 y' x h3) (@lem4804650 _110698 y' s r y x h1 h2)). Qed.
Lemma lem4804803 {_110698 : Type'} (r : type1402 _110698) (y : _110698) : (term394 _110698 r y) = (term394 _110698 r y).
Proof. exact (eq_refl (term394 _110698 r y)). Qed.
Lemma lem4804804 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (y' : _110698) (x : _110698) (h1 : y' = x) : (term395 _110698 r y y') = (term395 _110698 r y x).
Proof. exact (MK_COMB (@lem4804803 _110698 r y) (@lem4804470 _110698 y' x h1)). Qed.
Lemma lem4804805 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) : (term395 _110698 r y x) = (term359 _110698 r y x).
Proof. exact (eq_refl (term395 _110698 r y x)). Qed.
Lemma lem4804806 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (y' : _110698) : (term396 _110698 r y y') = (term396 _110698 r y y').
Proof. exact (eq_refl (term396 _110698 r y y')). Qed.
Lemma lem4804807 {_110698 : Type'} (y' : _110698) (r : type1402 _110698) (y : _110698) (x : _110698) : ((term395 _110698 r y y') = (term395 _110698 r y x)) = ((term395 _110698 r y y') = (term359 _110698 r y x)).
Proof. exact (MK_COMB (@lem4804806 _110698 r y y') (@lem4804805 _110698 r y x)). Qed.
Lemma lem4804808 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (y' : _110698) : (term395 _110698 r y y') = (term359 _110698 r y y').
Proof. exact (eq_refl (term395 _110698 r y y')). Qed.
Lemma lem4804809 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4804810 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (y' : _110698) : (term396 _110698 r y y') = (term397 _110698 r y y').
Proof. exact (MK_COMB (@lem4804809) (@lem4804808 _110698 r y y')). Qed.
Lemma lem4804811 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) : (term359 _110698 r y x) = (term359 _110698 r y x).
Proof. exact (eq_refl (term359 _110698 r y x)). Qed.
Lemma lem4804812 {_110698 : Type'} (y' : _110698) (r : type1402 _110698) (y : _110698) (x : _110698) : ((term395 _110698 r y y') = (term359 _110698 r y x)) = ((term359 _110698 r y y') = (term359 _110698 r y x)).
Proof. exact (MK_COMB (@lem4804810 _110698 r y y') (@lem4804811 _110698 r y x)). Qed.
Lemma lem4804813 {_110698 : Type'} (y' : _110698) (r : type1402 _110698) (y : _110698) (x : _110698) : ((term395 _110698 r y y') = (term395 _110698 r y x)) = ((term359 _110698 r y y') = (term359 _110698 r y x)).
Proof. exact (TRANS (@lem4804807 _110698 y' r y x) (@lem4804812 _110698 y' r y x)). Qed.
Lemma lem4804814 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (y' : _110698) (x : _110698) (h1 : y' = x) : (term359 _110698 r y y') = (term359 _110698 r y x).
Proof. exact (EQ_MP (@lem4804813 _110698 y' r y x) (@lem4804804 _110698 r y y' x h1)). Qed.
Lemma lem4804816 {_110698 : Type'} (y : _110698) : (term389 _110698 y) = (term389 _110698 y).
Proof. exact (eq_refl (term389 _110698 y)). Qed.
Lemma lem4804817 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (h1 : y' = x) : (term390 _110698 y y') = (term390 _110698 y x).
Proof. exact (MK_COMB (@lem4804816 _110698 y) (@lem4804470 _110698 y' x h1)). Qed.
Lemma lem4804818 {_110698 : Type'} (y : _110698) (x : _110698) : (term390 _110698 y x) = (term22 _110698 y x).
Proof. exact (eq_refl (term390 _110698 y x)). Qed.
Lemma lem4804819 {_110698 : Type'} (y : _110698) (y' : _110698) : (term393 _110698 y y') = (term393 _110698 y y').
Proof. exact (eq_refl (term393 _110698 y y')). Qed.
Lemma lem4804820 {_110698 : Type'} (y' : _110698) (y : _110698) (x : _110698) : ((term390 _110698 y y') = (term390 _110698 y x)) = ((term390 _110698 y y') = (term22 _110698 y x)).
Proof. exact (MK_COMB (@lem4804819 _110698 y y') (@lem4804818 _110698 y x)). Qed.
Lemma lem4804821 {_110698 : Type'} (y : _110698) (y' : _110698) : (term390 _110698 y y') = (term22 _110698 y y').
Proof. exact (eq_refl (term390 _110698 y y')). Qed.
Lemma lem4804822 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4804823 {_110698 : Type'} (y : _110698) (y' : _110698) : (term393 _110698 y y') = (term388 _110698 y y').
Proof. exact (MK_COMB (@lem4804822) (@lem4804821 _110698 y y')). Qed.
Lemma lem4804824 {_110698 : Type'} (y : _110698) (x : _110698) : (term22 _110698 y x) = (term22 _110698 y x).
Proof. exact (eq_refl (term22 _110698 y x)). Qed.
Lemma lem4804825 {_110698 : Type'} (y' : _110698) (y : _110698) (x : _110698) : ((term390 _110698 y y') = (term22 _110698 y x)) = ((term22 _110698 y y') = (term22 _110698 y x)).
Proof. exact (MK_COMB (@lem4804823 _110698 y y') (@lem4804824 _110698 y x)). Qed.
Lemma lem4804826 {_110698 : Type'} (y' : _110698) (y : _110698) (x : _110698) : ((term390 _110698 y y') = (term390 _110698 y x)) = ((term22 _110698 y y') = (term22 _110698 y x)).
Proof. exact (TRANS (@lem4804820 _110698 y' y x) (@lem4804825 _110698 y' y x)). Qed.
Lemma lem4804827 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (h1 : y' = x) : (term22 _110698 y y') = (term22 _110698 y x).
Proof. exact (EQ_MP (@lem4804826 _110698 y' y x) (@lem4804817 _110698 y y' x h1)). Qed.
Lemma lem4804828 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) : term22 _110698 y x.
Proof. exact (EQ_MP (@lem4804827 _110698 y y' x h2) (@lem4804468 _110698 y y' x s r h1)). Qed.
Lemma lem4804842 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) (h1 : @IN _110698 y s) : @IN _110698 y s.
Proof. exact (h1). Qed.
Lemma lem4804870 {_110698 : Type'} (_59439 : _110698) (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term383 _110698 s r _59439 x.
Proof. exact (EQ_MP (@lem4804495 _110698 s r _59439 x) (@lem4804155 _110698 _59439 y y' x s r h1)). Qed.
Lemma lem4804899 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) : (term398 _110698 r y') = (term398 _110698 r y').
Proof. exact (eq_refl (term398 _110698 r y')). Qed.
Lemma lem4804900 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (y : _110698) (x : _110698) (h1 : y = x) : (term399 _110698 r y' y) = (term399 _110698 r y' x).
Proof. exact (MK_COMB (@lem4804899 _110698 r y') (@lem4804522 _110698 y x h1)). Qed.
Lemma lem4804901 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (y' : _110698) : (term399 _110698 r y' x) = (term359 _110698 r x y').
Proof. exact (eq_refl (term399 _110698 r y' x)). Qed.
Lemma lem4804902 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (y : _110698) : (term400 _110698 r y' y) = (term400 _110698 r y' y).
Proof. exact (eq_refl (term400 _110698 r y' y)). Qed.
Lemma lem4804903 {_110698 : Type'} (y : _110698) (r : type1402 _110698) (x : _110698) (y' : _110698) : ((term399 _110698 r y' y) = (term399 _110698 r y' x)) = ((term399 _110698 r y' y) = (term359 _110698 r x y')).
Proof. exact (MK_COMB (@lem4804902 _110698 r y' y) (@lem4804901 _110698 r x y')). Qed.
Lemma lem4804904 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (y' : _110698) : (term399 _110698 r y' y) = (term359 _110698 r y y').
Proof. exact (eq_refl (term399 _110698 r y' y)). Qed.
Lemma lem4804905 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4804906 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (y' : _110698) : (term400 _110698 r y' y) = (term397 _110698 r y y').
Proof. exact (MK_COMB (@lem4804905) (@lem4804904 _110698 r y y')). Qed.
Lemma lem4804907 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (y' : _110698) : (term359 _110698 r x y') = (term359 _110698 r x y').
Proof. exact (eq_refl (term359 _110698 r x y')). Qed.
Lemma lem4804908 {_110698 : Type'} (y : _110698) (r : type1402 _110698) (x : _110698) (y' : _110698) : ((term399 _110698 r y' y) = (term359 _110698 r x y')) = ((term359 _110698 r y y') = (term359 _110698 r x y')).
Proof. exact (MK_COMB (@lem4804906 _110698 r y y') (@lem4804907 _110698 r x y')). Qed.
Lemma lem4804909 {_110698 : Type'} (y : _110698) (r : type1402 _110698) (x : _110698) (y' : _110698) : ((term399 _110698 r y' y) = (term399 _110698 r y' x)) = ((term359 _110698 r y y') = (term359 _110698 r x y')).
Proof. exact (TRANS (@lem4804903 _110698 y r x y') (@lem4804908 _110698 y r x y')). Qed.
Lemma lem4804910 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (y : _110698) (x : _110698) (h1 : y = x) : (term359 _110698 r y y') = (term359 _110698 r x y').
Proof. exact (EQ_MP (@lem4804909 _110698 y r x y') (@lem4804900 _110698 r y' y x h1)). Qed.
Lemma lem4804912 {_110698 : Type'} (y' : _110698) : (term385 _110698 y') = (term385 _110698 y').
Proof. exact (eq_refl (term385 _110698 y')). Qed.
Lemma lem4804913 {_110698 : Type'} (y' : _110698) (y : _110698) (x : _110698) (h1 : y = x) : (term386 _110698 y' y) = (term386 _110698 y' x).
Proof. exact (MK_COMB (@lem4804912 _110698 y') (@lem4804522 _110698 y x h1)). Qed.
Lemma lem4804914 {_110698 : Type'} (x : _110698) (y' : _110698) : (term386 _110698 y' x) = (term22 _110698 x y').
Proof. exact (eq_refl (term386 _110698 y' x)). Qed.
Lemma lem4804915 {_110698 : Type'} (y' : _110698) (y : _110698) : (term387 _110698 y' y) = (term387 _110698 y' y).
Proof. exact (eq_refl (term387 _110698 y' y)). Qed.
Lemma lem4804916 {_110698 : Type'} (y : _110698) (x : _110698) (y' : _110698) : ((term386 _110698 y' y) = (term386 _110698 y' x)) = ((term386 _110698 y' y) = (term22 _110698 x y')).
Proof. exact (MK_COMB (@lem4804915 _110698 y' y) (@lem4804914 _110698 x y')). Qed.
Lemma lem4804917 {_110698 : Type'} (y : _110698) (y' : _110698) : (term386 _110698 y' y) = (term22 _110698 y y').
Proof. exact (eq_refl (term386 _110698 y' y)). Qed.
Lemma lem4804918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4804919 {_110698 : Type'} (y : _110698) (y' : _110698) : (term387 _110698 y' y) = (term388 _110698 y y').
Proof. exact (MK_COMB (@lem4804918) (@lem4804917 _110698 y y')). Qed.
Lemma lem4804920 {_110698 : Type'} (x : _110698) (y' : _110698) : (term22 _110698 x y') = (term22 _110698 x y').
Proof. exact (eq_refl (term22 _110698 x y')). Qed.
Lemma lem4804921 {_110698 : Type'} (y : _110698) (x : _110698) (y' : _110698) : ((term386 _110698 y' y) = (term22 _110698 x y')) = ((term22 _110698 y y') = (term22 _110698 x y')).
Proof. exact (MK_COMB (@lem4804919 _110698 y y') (@lem4804920 _110698 x y')). Qed.
Lemma lem4804922 {_110698 : Type'} (y : _110698) (x : _110698) (y' : _110698) : ((term386 _110698 y' y) = (term386 _110698 y' x)) = ((term22 _110698 y y') = (term22 _110698 x y')).
Proof. exact (TRANS (@lem4804916 _110698 y x y') (@lem4804921 _110698 y x y')). Qed.
Lemma lem4804923 {_110698 : Type'} (y' : _110698) (y : _110698) (x : _110698) (h1 : y = x) : (term22 _110698 y y') = (term22 _110698 x y').
Proof. exact (EQ_MP (@lem4804922 _110698 y x y') (@lem4804913 _110698 y' y x h1)). Qed.
Lemma lem4804924 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) : term22 _110698 x y'.
Proof. exact (EQ_MP (@lem4804923 _110698 y' y x h2) (@lem4804518 _110698 y y' x s r h1)). Qed.
Lemma lem4804938 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (h1 : @IN _110698 y' s) : @IN _110698 y' s.
Proof. exact (h1). Qed.
Lemma lem4804952 {_110698 : Type'} (_59442 : _110698) (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term384 _110698 s r x _59442.
Proof. exact (EQ_MP (@lem4804533 _110698 s r x _59442) (@lem4804158 _110698 _59442 y y' x s r h1)). Qed.
Lemma lem4805008 {_110698 : Type'} (x : _110698) (y : _110698) (z : _110698) : term401 _110698 x y z.
Proof. exact (@lem21385 _110698 x y z). Qed.
Lemma lem4805010 {_110698 : Type'} (x : _110698) : x = x.
Proof. exact (@lem21386 _110698 x). Qed.
Lemma lem4805011 {_110698 : Type'} (x : _110698) : x = x.
Proof. exact (@lem4805010 _110698 x). Qed.
Lemma lem4805012 {_110698 : Type'} (x : _110698) : term402 _110698 x.
Proof. exact (fun h0 : term392 _110698 x => @lem4805011 _110698 x). Qed.
Lemma lem4805014 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4805015 {_110698 : Type'} (x : _110698) : (term402 _110698 x) = (x = x).
Proof. exact (@lem4805014 (x = x)). Qed.
Lemma lem4805016 {_110698 : Type'} (x : _110698) : x = x.
Proof. exact (EQ_MP (@lem4805015 _110698 x) (@lem4805012 _110698 x)). Qed.
Lemma lem4805018 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term118 _110698 s r y x) : @IN _110698 y s.
Proof. exact (proj1 (@lem4803488 _110698 s r y x h1)). Qed.
Lemma lem4805019 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term118 _110698 s r y x) : term404 _110698 y s.
Proof. exact (fun h0 : term331 _110698 y s => @lem4805018 _110698 s r y x h1). Qed.
Lemma lem4805021 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4805022 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) : (term404 _110698 y s) = (@IN _110698 y s).
Proof. exact (@lem4805021 (@IN _110698 y s)). Qed.
Lemma lem4805023 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term118 _110698 s r y x) : @IN _110698 y s.
Proof. exact (EQ_MP (@lem4805022 _110698 y s) (@lem4805019 _110698 s r y x h1)). Qed.
Lemma lem4805025 {_110698 : Type'} (x : _110698) : x = x.
Proof. exact (@lem21386 _110698 x). Qed.
Lemma lem4805026 {_110698 : Type'} (x : _110698) : x = x.
Proof. exact (@lem4805025 _110698 x). Qed.
Lemma lem4805027 {_110698 : Type'} (x : _110698) : term402 _110698 x.
Proof. exact (fun h0 : term392 _110698 x => @lem4805026 _110698 x). Qed.
Lemma lem4805029 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4805030 {_110698 : Type'} (x : _110698) : (term402 _110698 x) = (x = x).
Proof. exact (@lem4805029 (x = x)). Qed.
Lemma lem4805031 {_110698 : Type'} (x : _110698) : x = x.
Proof. exact (EQ_MP (@lem4805030 _110698 x) (@lem4805027 _110698 x)). Qed.
Lemma lem4805033 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term118 _110698 s r y x) : term22 _110698 y x.
Proof. exact (proj2 (@lem4803488 _110698 s r y x h1)). Qed.
Lemma lem4805034 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term118 _110698 s r y x) : term405 _110698 y x.
Proof. exact (fun h0 : y = x => @lem4805033 _110698 s r y x h1). Qed.
Lemma lem4805036 (p : Prop) : (term406 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4805037 {_110698 : Type'} (y : _110698) (x : _110698) : (term405 _110698 y x) = (term22 _110698 y x).
Proof. exact (@lem4805036 (y = x)). Qed.
Lemma lem4805038 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term118 _110698 s r y x) : term22 _110698 y x.
Proof. exact (EQ_MP (@lem4805037 _110698 y x) (@lem4805034 _110698 s r y x h1)). Qed.
Lemma lem4805040 (b : Prop) (a : Prop) : (a \/ b) = (term407 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4805041 {_110698 : Type'} (z : _110698) (x : _110698) (y : _110698) : (term401 _110698 x y z) = (term408 _110698 z x y).
Proof. exact (@lem4805040 (term409 _110698 x y z) (term22 _110698 x y)). Qed.
Lemma lem4805043 (a : Prop) (b : Prop) : (term410 a b) = (term411 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4805044 {_110698 : Type'} (x : _110698) (y : _110698) (z : _110698) : (term412 _110698 x y z) = (term413 _110698 x y z).
Proof. exact (@lem4805043 (term22 _110698 x z) (y = z)). Qed.
Lemma lem4805046 (a : Prop) : (term62 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4805047 {_110698 : Type'} (x : _110698) (z : _110698) : (term74 _110698 x z) = (x = z).
Proof. exact (@lem4805046 (x = z)). Qed.
Lemma lem4805048 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4805049 {_110698 : Type'} (x : _110698) (z : _110698) : (term414 _110698 x z) = (term415 _110698 x z).
Proof. exact (MK_COMB (@lem4805048) (@lem4805047 _110698 x z)). Qed.
Lemma lem4805050 {_110698 : Type'} (y : _110698) (z : _110698) : (term22 _110698 y z) = (term22 _110698 y z).
Proof. exact (eq_refl (term22 _110698 y z)). Qed.
Lemma lem4805051 {_110698 : Type'} (x : _110698) (y : _110698) (z : _110698) : (term413 _110698 x y z) = (term416 _110698 x y z).
Proof. exact (MK_COMB (@lem4805049 _110698 x z) (@lem4805050 _110698 y z)). Qed.
Lemma lem4805052 {_110698 : Type'} (x : _110698) (y : _110698) (z : _110698) : (term412 _110698 x y z) = (term416 _110698 x y z).
Proof. exact (TRANS (@lem4805044 _110698 x y z) (@lem4805051 _110698 x y z)). Qed.
Lemma lem4805053 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4805054 {_110698 : Type'} (x : _110698) (y : _110698) (z : _110698) : (term417 _110698 x y z) = (term418 _110698 x y z).
Proof. exact (MK_COMB (@lem4805053) (@lem4805052 _110698 x y z)). Qed.
Lemma lem4805055 {_110698 : Type'} (x : _110698) (y : _110698) : (term22 _110698 x y) = (term22 _110698 x y).
Proof. exact (eq_refl (term22 _110698 x y)). Qed.
Lemma lem4805056 {_110698 : Type'} (z : _110698) (x : _110698) (y : _110698) : (term408 _110698 z x y) = (term419 _110698 z x y).
Proof. exact (MK_COMB (@lem4805054 _110698 x y z) (@lem4805055 _110698 x y)). Qed.
Lemma lem4805057 {_110698 : Type'} (z : _110698) (x : _110698) (y : _110698) : (term401 _110698 x y z) = (term419 _110698 z x y).
Proof. exact (TRANS (@lem4805041 _110698 z x y) (@lem4805056 _110698 z x y)). Qed.
Lemma lem4805059 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term118 _110698 s r y x) : term420 _110698 y x.
Proof. exact (conj (@lem4805031 _110698 x) (@lem4805038 _110698 s r y x h1)). Qed.
Lemma lem4805061 {_110698 : Type'} (z : _110698) (x : _110698) (y : _110698) : term419 _110698 z x y.
Proof. exact (EQ_MP (@lem4805057 _110698 z x y) (@lem4805008 _110698 x y z)). Qed.
Lemma lem4805062 {_110698 : Type'} (z : _110698) (x : _110698) (y : _110698) : term419 _110698 z x y.
Proof. exact (@lem4805061 _110698 z x y). Qed.
Lemma lem4805063 {_110698 : Type'} (x : _110698) (y : _110698) : term421 _110698 x y.
Proof. exact (@lem4805062 _110698 x x y). Qed.
Lemma lem4805066 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term118 _110698 s r y x) : term22 _110698 x y.
Proof. exact (@lem4805063 _110698 x y (@lem4805059 _110698 s r y x h1)). Qed.
Lemma lem4805067 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term118 _110698 s r y x) : term405 _110698 x y.
Proof. exact (fun h0 : x = y => @lem4805066 _110698 s r y x h1). Qed.
Lemma lem4805069 (p : Prop) : (term406 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4805070 {_110698 : Type'} (x : _110698) (y : _110698) : (term405 _110698 x y) = (term22 _110698 x y).
Proof. exact (@lem4805069 (x = y)). Qed.
Lemma lem4805071 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term118 _110698 s r y x) : term22 _110698 x y.
Proof. exact (EQ_MP (@lem4805070 _110698 x y) (@lem4805067 _110698 s r y x h1)). Qed.
Lemma lem4805089 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4805090 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59430 : _110698) (_59431 : _110698) : (term374 _110698 s r _59430 _59431) = (term422 _110698 s r _59430 _59431).
Proof. exact (@lem4805089 (_59430 = _59431) (term331 _110698 _59431 s) (r _59430 _59431)). Qed.
Lemma lem4805106 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4805107 {_110698 : Type'} (r : type1402 _110698) (_59430 : _110698) (_59431 : _110698) (s : _110698 -> Prop) : (term423 _110698 s r _59430 _59431) = (term424 _110698 r _59430 _59431 s).
Proof. exact (@lem4805106 (r _59430 _59431) (term331 _110698 _59431 s)). Qed.
Lemma lem4805113 {_110698 : Type'} (_59430 : _110698) (_59431 : _110698) : (term425 _110698 _59430 _59431) = (term425 _110698 _59430 _59431).
Proof. exact (eq_refl (term425 _110698 _59430 _59431)). Qed.
Lemma lem4805114 {_110698 : Type'} (r : type1402 _110698) (_59430 : _110698) (_59431 : _110698) (s : _110698 -> Prop) : (term422 _110698 s r _59430 _59431) = (term426 _110698 r _59430 _59431 s).
Proof. exact (MK_COMB (@lem4805113 _110698 _59430 _59431) (@lem4805107 _110698 r _59430 _59431 s)). Qed.
Lemma lem4805118 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4805119 {_110698 : Type'} (r : type1402 _110698) (_59430 : _110698) (_59431 : _110698) (s : _110698 -> Prop) : (term426 _110698 r _59430 _59431 s) = (term427 _110698 r _59430 _59431 s).
Proof. exact (@lem4805118 (r _59430 _59431) (_59430 = _59431) (term331 _110698 _59431 s)). Qed.
Lemma lem4805137 {_110698 : Type'} (r : type1402 _110698) (_59430 : _110698) (_59431 : _110698) (s : _110698 -> Prop) : (term422 _110698 s r _59430 _59431) = (term427 _110698 r _59430 _59431 s).
Proof. exact (TRANS (@lem4805114 _110698 r _59430 _59431 s) (@lem4805119 _110698 r _59430 _59431 s)). Qed.
Lemma lem4805138 {_110698 : Type'} (r : type1402 _110698) (_59430 : _110698) (_59431 : _110698) (s : _110698 -> Prop) : (term374 _110698 s r _59430 _59431) = (term427 _110698 r _59430 _59431 s).
Proof. exact (TRANS (@lem4805090 _110698 s r _59430 _59431) (@lem4805137 _110698 r _59430 _59431 s)). Qed.
Lemma lem4805139 {_110698 : Type'} (_59430 : _110698) (x : _110698) : (term375 _110698 _59430 x) = (term375 _110698 _59430 x).
Proof. exact (eq_refl (term375 _110698 _59430 x)). Qed.
Lemma lem4805140 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (_59430 : _110698) (_59431 : _110698) (s : _110698 -> Prop) : (term376 _110698 x s r _59430 _59431) = (term428 _110698 x r _59430 _59431 s).
Proof. exact (MK_COMB (@lem4805139 _110698 _59430 x) (@lem4805138 _110698 r _59430 _59431 s)). Qed.
Lemma lem4805144 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4805145 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59430 : _110698) (_59431 : _110698) (s : _110698 -> Prop) : (term428 _110698 x r _59430 _59431 s) = (term429 _110698 r x _59430 _59431 s).
Proof. exact (@lem4805144 (r _59430 _59431) (term22 _110698 _59430 x) (term430 _110698 _59430 _59431 s)). Qed.
Lemma lem4805159 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4805160 {_110698 : Type'} (_59430 : _110698) (x : _110698) (_59431 : _110698) (s : _110698 -> Prop) : (term431 _110698 x _59430 _59431 s) = (term432 _110698 _59430 x _59431 s).
Proof. exact (@lem4805159 (_59430 = _59431) (term22 _110698 _59430 x) (term331 _110698 _59431 s)). Qed.
Lemma lem4805180 {_110698 : Type'} (r : type1402 _110698) (_59430 : _110698) (_59431 : _110698) : (term433 _110698 r _59430 _59431) = (term433 _110698 r _59430 _59431).
Proof. exact (eq_refl (term433 _110698 r _59430 _59431)). Qed.
Lemma lem4805181 {_110698 : Type'} (r : type1402 _110698) (_59430 : _110698) (x : _110698) (_59431 : _110698) (s : _110698 -> Prop) : (term429 _110698 r x _59430 _59431 s) = (term434 _110698 r _59430 x _59431 s).
Proof. exact (MK_COMB (@lem4805180 _110698 r _59430 _59431) (@lem4805160 _110698 _59430 x _59431 s)). Qed.
Lemma lem4805192 {_110698 : Type'} (r : type1402 _110698) (_59430 : _110698) (x : _110698) (_59431 : _110698) (s : _110698 -> Prop) : (term428 _110698 x r _59430 _59431 s) = (term434 _110698 r _59430 x _59431 s).
Proof. exact (TRANS (@lem4805145 _110698 r x _59430 _59431 s) (@lem4805181 _110698 r _59430 x _59431 s)). Qed.
Lemma lem4805193 {_110698 : Type'} (r : type1402 _110698) (_59430 : _110698) (x : _110698) (_59431 : _110698) (s : _110698 -> Prop) : (term376 _110698 x s r _59430 _59431) = (term434 _110698 r _59430 x _59431 s).
Proof. exact (TRANS (@lem4805140 _110698 x r _59430 _59431 s) (@lem4805192 _110698 r _59430 x _59431 s)). Qed.
Lemma lem4805194 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4805195 {_110698 : Type'} (r : type1402 _110698) (_59430 : _110698) (x : _110698) (_59431 : _110698) (s : _110698 -> Prop) : (term435 _110698 x s r _59430 _59431) = (term436 _110698 r _59430 x _59431 s).
Proof. exact (MK_COMB (@lem4805194) (@lem4805193 _110698 r _59430 x _59431 s)). Qed.
Lemma lem4805221 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4805222 {_110698 : Type'} (_59430 : _110698) (_59431 : _110698) (s : _110698 -> Prop) : (term135 _110698 s _59430 _59431) = (term430 _110698 _59430 _59431 s).
Proof. exact (@lem4805221 (_59430 = _59431) (term331 _110698 _59431 s)). Qed.
Lemma lem4805230 {_110698 : Type'} (_59430 : _110698) (x : _110698) : (term375 _110698 _59430 x) = (term375 _110698 _59430 x).
Proof. exact (eq_refl (term375 _110698 _59430 x)). Qed.
Lemma lem4805231 {_110698 : Type'} (x : _110698) (_59430 : _110698) (_59431 : _110698) (s : _110698 -> Prop) : (term347 _110698 x s _59430 _59431) = (term431 _110698 x _59430 _59431 s).
Proof. exact (MK_COMB (@lem4805230 _110698 _59430 x) (@lem4805222 _110698 _59430 _59431 s)). Qed.
Lemma lem4805235 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4805236 {_110698 : Type'} (_59430 : _110698) (x : _110698) (_59431 : _110698) (s : _110698 -> Prop) : (term431 _110698 x _59430 _59431 s) = (term432 _110698 _59430 x _59431 s).
Proof. exact (@lem4805235 (_59430 = _59431) (term22 _110698 _59430 x) (term331 _110698 _59431 s)). Qed.
Lemma lem4805256 {_110698 : Type'} (_59430 : _110698) (x : _110698) (_59431 : _110698) (s : _110698 -> Prop) : (term347 _110698 x s _59430 _59431) = (term432 _110698 _59430 x _59431 s).
Proof. exact (TRANS (@lem4805231 _110698 x _59430 _59431 s) (@lem4805236 _110698 _59430 x _59431 s)). Qed.
Lemma lem4805257 {_110698 : Type'} (r : type1402 _110698) (_59430 : _110698) (_59431 : _110698) : (term433 _110698 r _59430 _59431) = (term433 _110698 r _59430 _59431).
Proof. exact (eq_refl (term433 _110698 r _59430 _59431)). Qed.
Lemma lem4805258 {_110698 : Type'} (r : type1402 _110698) (_59430 : _110698) (x : _110698) (_59431 : _110698) (s : _110698 -> Prop) : (term437 _110698 r x s _59430 _59431) = (term434 _110698 r _59430 x _59431 s).
Proof. exact (MK_COMB (@lem4805257 _110698 r _59430 _59431) (@lem4805256 _110698 _59430 x _59431 s)). Qed.
Lemma lem4805269 {_110698 : Type'} (r : type1402 _110698) (_59430 : _110698) (x : _110698) (_59431 : _110698) (s : _110698 -> Prop) : ((term376 _110698 x s r _59430 _59431) = (term437 _110698 r x s _59430 _59431)) = ((term434 _110698 r _59430 x _59431 s) = (term434 _110698 r _59430 x _59431 s)).
Proof. exact (MK_COMB (@lem4805195 _110698 r _59430 x _59431 s) (@lem4805258 _110698 r _59430 x _59431 s)). Qed.
Lemma lem4805271 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4805272 (x : Prop) : (x = x) = True.
Proof. exact (@lem4805271 Prop x). Qed.
Lemma lem4805273 {_110698 : Type'} (r : type1402 _110698) (_59430 : _110698) (x : _110698) (_59431 : _110698) (s : _110698 -> Prop) : ((term434 _110698 r _59430 x _59431 s) = (term434 _110698 r _59430 x _59431 s)) = True.
Proof. exact (@lem4805272 (term434 _110698 r _59430 x _59431 s)). Qed.
Lemma lem4805274 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (s : _110698 -> Prop) (_59430 : _110698) (_59431 : _110698) : ((term376 _110698 x s r _59430 _59431) = (term437 _110698 r x s _59430 _59431)) = True.
Proof. exact (TRANS (@lem4805269 _110698 r _59430 x _59431 s) (@lem4805273 _110698 r _59430 x _59431 s)). Qed.
Lemma lem4805275 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (s : _110698 -> Prop) (_59430 : _110698) (_59431 : _110698) : True = ((term376 _110698 x s r _59430 _59431) = (term437 _110698 r x s _59430 _59431)).
Proof. exact (SYM (@lem4805274 _110698 r x s _59430 _59431)). Qed.
Lemma lem4805276 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (s : _110698 -> Prop) (_59430 : _110698) (_59431 : _110698) : (term376 _110698 x s r _59430 _59431) = (term437 _110698 r x s _59430 _59431).
Proof. exact (EQ_MP (@lem4805275 _110698 r x s _59430 _59431) (@lem0)). Qed.
Lemma lem4805277 {_110698 : Type'} (_59430 : _110698) (_59431 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term437 _110698 r x s _59430 _59431.
Proof. exact (EQ_MP (@lem4805276 _110698 r x s _59430 _59431) (@lem4804184 _110698 _59430 _59431 x s r y y' h1)). Qed.
Lemma lem4805279 (b : Prop) (a : Prop) : (a \/ b) = (term407 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4805280 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (_59430 : _110698) (_59431 : _110698) : (term437 _110698 r x s _59430 _59431) = (term438 _110698 x s r _59430 _59431).
Proof. exact (@lem4805279 (term347 _110698 x s _59430 _59431) (r _59430 _59431)). Qed.
Lemma lem4805282 (a : Prop) (b : Prop) : (term410 a b) = (term411 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4805283 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (_59430 : _110698) (_59431 : _110698) : (term439 _110698 x s _59430 _59431) = (term440 _110698 x s _59430 _59431).
Proof. exact (@lem4805282 (term22 _110698 _59430 x) (term135 _110698 s _59430 _59431)). Qed.
Lemma lem4805285 (a : Prop) : (term62 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4805286 {_110698 : Type'} (_59430 : _110698) (x : _110698) : (term74 _110698 _59430 x) = (_59430 = x).
Proof. exact (@lem4805285 (_59430 = x)). Qed.
Lemma lem4805287 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4805288 {_110698 : Type'} (_59430 : _110698) (x : _110698) : (term414 _110698 _59430 x) = (term415 _110698 _59430 x).
Proof. exact (MK_COMB (@lem4805287) (@lem4805286 _110698 _59430 x)). Qed.
Lemma lem4805290 (a : Prop) (b : Prop) : (term410 a b) = (term411 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4805291 {_110698 : Type'} (s : _110698 -> Prop) (_59430 : _110698) (_59431 : _110698) : (term441 _110698 s _59430 _59431) = (term442 _110698 s _59430 _59431).
Proof. exact (@lem4805290 (term331 _110698 _59431 s) (_59430 = _59431)). Qed.
Lemma lem4805293 (a : Prop) : (term62 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4805294 {_110698 : Type'} (_59431 : _110698) (s : _110698 -> Prop) : (term443 _110698 _59431 s) = (@IN _110698 _59431 s).
Proof. exact (@lem4805293 (@IN _110698 _59431 s)). Qed.
Lemma lem4805295 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4805296 {_110698 : Type'} (_59431 : _110698) (s : _110698 -> Prop) : (term444 _110698 _59431 s) = (term445 _110698 _59431 s).
Proof. exact (MK_COMB (@lem4805295) (@lem4805294 _110698 _59431 s)). Qed.
Lemma lem4805297 {_110698 : Type'} (_59430 : _110698) (_59431 : _110698) : (term22 _110698 _59430 _59431) = (term22 _110698 _59430 _59431).
Proof. exact (eq_refl (term22 _110698 _59430 _59431)). Qed.
Lemma lem4805298 {_110698 : Type'} (s : _110698 -> Prop) (_59430 : _110698) (_59431 : _110698) : (term442 _110698 s _59430 _59431) = (term140 _110698 s _59430 _59431).
Proof. exact (MK_COMB (@lem4805296 _110698 _59431 s) (@lem4805297 _110698 _59430 _59431)). Qed.
Lemma lem4805299 {_110698 : Type'} (s : _110698 -> Prop) (_59430 : _110698) (_59431 : _110698) : (term441 _110698 s _59430 _59431) = (term140 _110698 s _59430 _59431).
Proof. exact (TRANS (@lem4805291 _110698 s _59430 _59431) (@lem4805298 _110698 s _59430 _59431)). Qed.
Lemma lem4805300 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (_59430 : _110698) (_59431 : _110698) : (term440 _110698 x s _59430 _59431) = (term446 _110698 x s _59430 _59431).
Proof. exact (MK_COMB (@lem4805288 _110698 _59430 x) (@lem4805299 _110698 s _59430 _59431)). Qed.
Lemma lem4805301 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (_59430 : _110698) (_59431 : _110698) : (term439 _110698 x s _59430 _59431) = (term446 _110698 x s _59430 _59431).
Proof. exact (TRANS (@lem4805283 _110698 x s _59430 _59431) (@lem4805300 _110698 x s _59430 _59431)). Qed.
Lemma lem4805302 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4805303 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (_59430 : _110698) (_59431 : _110698) : (term447 _110698 x s _59430 _59431) = (term448 _110698 x s _59430 _59431).
Proof. exact (MK_COMB (@lem4805302) (@lem4805301 _110698 x s _59430 _59431)). Qed.
Lemma lem4805304 {_110698 : Type'} (r : type1402 _110698) (_59430 : _110698) (_59431 : _110698) : (r _59430 _59431) = (r _59430 _59431).
Proof. exact (eq_refl (r _59430 _59431)). Qed.
Lemma lem4805305 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (_59430 : _110698) (_59431 : _110698) : (term438 _110698 x s r _59430 _59431) = (term449 _110698 x s r _59430 _59431).
Proof. exact (MK_COMB (@lem4805303 _110698 x s _59430 _59431) (@lem4805304 _110698 r _59430 _59431)). Qed.
Lemma lem4805306 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (_59430 : _110698) (_59431 : _110698) : (term437 _110698 r x s _59430 _59431) = (term449 _110698 x s r _59430 _59431).
Proof. exact (TRANS (@lem4805280 _110698 x s r _59430 _59431) (@lem4805305 _110698 x s r _59430 _59431)). Qed.
Lemma lem4805308 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term118 _110698 s r y x) : term140 _110698 s x y.
Proof. exact (conj (@lem4805023 _110698 s r y x h1) (@lem4805071 _110698 s r y x h1)). Qed.
Lemma lem4805309 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term118 _110698 s r y x) : term450 _110698 s x y.
Proof. exact (conj (@lem4805016 _110698 x) (@lem4805308 _110698 s r y x h1)). Qed.
Lemma lem4805311 {_110698 : Type'} (_59430 : _110698) (_59431 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term449 _110698 x s r _59430 _59431.
Proof. exact (EQ_MP (@lem4805306 _110698 x s r _59430 _59431) (@lem4805277 _110698 _59430 _59431 x s r y y' h1)). Qed.
Lemma lem4805312 {_110698 : Type'} (_59430 : _110698) (_59431 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term449 _110698 x s r _59430 _59431.
Proof. exact (@lem4805311 _110698 _59430 _59431 x s r y y' h1). Qed.
Lemma lem4805313 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term451 _110698 s r x y.
Proof. exact (@lem4805312 _110698 x y x s r y y' h1). Qed.
Lemma lem4805316 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term247 _110698 x s r y y') (h2 : term118 _110698 s r y x) : r x y.
Proof. exact (@lem4805313 _110698 x s r y y' h1 (@lem4805309 _110698 s r y x h2)). Qed.
Lemma lem4805317 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term247 _110698 x s r y y') (h2 : term118 _110698 s r y x) : term452 _110698 r x y.
Proof. exact (fun h0 : term359 _110698 r x y => @lem4805316 _110698 y' s r y x h1 h2). Qed.
Lemma lem4805319 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4805320 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (y : _110698) : (term452 _110698 r x y) = (r x y).
Proof. exact (@lem4805319 (r x y)). Qed.
Lemma lem4805321 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term247 _110698 x s r y y') (h2 : term118 _110698 s r y x) : r x y.
Proof. exact (EQ_MP (@lem4805320 _110698 r x y) (@lem4805317 _110698 y' s r y x h1 h2)). Qed.
Lemma lem4805324 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4805326 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (y : _110698) : (term359 _110698 r x y) = (term453 _110698 r x y).
Proof. exact (@lem4805324 (r x y)). Qed.
Lemma lem4805329 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (y : _110698) (h1 : term359 _110698 r x y) : term453 _110698 r x y.
Proof. exact (EQ_MP (@lem4805326 _110698 r x y) (@lem4804166 _110698 r x y h1)). Qed.
Lemma lem4805332 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term359 _110698 r x y) (h2 : term247 _110698 x s r y y') (h3 : term118 _110698 s r y x) : False.
Proof. exact (@lem4805329 _110698 r x y h1 (@lem4805321 _110698 y' s r y x h2 h3)). Qed.
Lemma lem4805333 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term359 _110698 r x y) (h2 : term247 _110698 x s r y y') (h3 : term118 _110698 s r y x) : term454.
Proof. exact (fun h0 : ~ False => @lem4805332 _110698 y' s r y x h1 h2 h3). Qed.
Lemma lem4805335 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4805336 : term454 = False.
Proof. exact (@lem4805335 False). Qed.
Lemma lem4805337 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term359 _110698 r x y) (h2 : term247 _110698 x s r y y') (h3 : term118 _110698 s r y x) : False.
Proof. exact (EQ_MP (@lem4805336) (@lem4805333 _110698 y' s r y x h1 h2 h3)). Qed.
Lemma lem4805381 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term118 _110698 s r y x) : @IN _110698 y s.
Proof. exact (proj1 (@lem4803488 _110698 s r y x h1)). Qed.
Lemma lem4805382 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term118 _110698 s r y x) : term404 _110698 y s.
Proof. exact (fun h0 : term331 _110698 y s => @lem4805381 _110698 s r y x h1). Qed.
Lemma lem4805384 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4805385 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) : (term404 _110698 y s) = (@IN _110698 y s).
Proof. exact (@lem4805384 (@IN _110698 y s)). Qed.
Lemma lem4805386 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term118 _110698 s r y x) : @IN _110698 y s.
Proof. exact (EQ_MP (@lem4805385 _110698 y s) (@lem4805382 _110698 s r y x h1)). Qed.
Lemma lem4805388 {_110698 : Type'} (x : _110698) : x = x.
Proof. exact (@lem21386 _110698 x). Qed.
Lemma lem4805389 {_110698 : Type'} (x : _110698) : x = x.
Proof. exact (@lem4805388 _110698 x). Qed.
Lemma lem4805390 {_110698 : Type'} (x : _110698) : term402 _110698 x.
Proof. exact (fun h0 : term392 _110698 x => @lem4805389 _110698 x). Qed.
Lemma lem4805392 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4805393 {_110698 : Type'} (x : _110698) : (term402 _110698 x) = (x = x).
Proof. exact (@lem4805392 (x = x)). Qed.
Lemma lem4805394 {_110698 : Type'} (x : _110698) : x = x.
Proof. exact (EQ_MP (@lem4805393 _110698 x) (@lem4805390 _110698 x)). Qed.
Lemma lem4805396 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term118 _110698 s r y x) : term22 _110698 y x.
Proof. exact (proj2 (@lem4803488 _110698 s r y x h1)). Qed.
Lemma lem4805397 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term118 _110698 s r y x) : term405 _110698 y x.
Proof. exact (fun h0 : y = x => @lem4805396 _110698 s r y x h1). Qed.
Lemma lem4805399 (p : Prop) : (term406 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4805400 {_110698 : Type'} (y : _110698) (x : _110698) : (term405 _110698 y x) = (term22 _110698 y x).
Proof. exact (@lem4805399 (y = x)). Qed.
Lemma lem4805401 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term118 _110698 s r y x) : term22 _110698 y x.
Proof. exact (EQ_MP (@lem4805400 _110698 y x) (@lem4805397 _110698 s r y x h1)). Qed.
Lemma lem4805407 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4805408 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (_59432 : _110698) (_59433 : _110698) : (term380 _110698 s x r _59432 _59433) = (term455 _110698 x s r _59432 _59433).
Proof. exact (@lem4805407 (term22 _110698 _59433 x) (term331 _110698 _59432 s) (term456 _110698 r _59432 _59433)). Qed.
Lemma lem4805424 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4805425 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59432 : _110698) (_59433 : _110698) : (term383 _110698 s r _59432 _59433) = (term457 _110698 s r _59432 _59433).
Proof. exact (@lem4805424 (_59432 = _59433) (term331 _110698 _59432 s) (r _59432 _59433)). Qed.
Lemma lem4805441 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4805442 {_110698 : Type'} (r : type1402 _110698) (_59433 : _110698) (_59432 : _110698) (s : _110698 -> Prop) : (term458 _110698 s r _59432 _59433) = (term459 _110698 r _59433 _59432 s).
Proof. exact (@lem4805441 (r _59432 _59433) (term331 _110698 _59432 s)). Qed.
Lemma lem4805448 {_110698 : Type'} (_59432 : _110698) (_59433 : _110698) : (term425 _110698 _59432 _59433) = (term425 _110698 _59432 _59433).
Proof. exact (eq_refl (term425 _110698 _59432 _59433)). Qed.
Lemma lem4805449 {_110698 : Type'} (r : type1402 _110698) (_59433 : _110698) (_59432 : _110698) (s : _110698 -> Prop) : (term457 _110698 s r _59432 _59433) = (term460 _110698 r _59433 _59432 s).
Proof. exact (MK_COMB (@lem4805448 _110698 _59432 _59433) (@lem4805442 _110698 r _59433 _59432 s)). Qed.
Lemma lem4805453 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4805454 {_110698 : Type'} (r : type1402 _110698) (_59433 : _110698) (_59432 : _110698) (s : _110698 -> Prop) : (term460 _110698 r _59433 _59432 s) = (term461 _110698 r _59433 _59432 s).
Proof. exact (@lem4805453 (r _59432 _59433) (_59432 = _59433) (term331 _110698 _59432 s)). Qed.
Lemma lem4805472 {_110698 : Type'} (r : type1402 _110698) (_59433 : _110698) (_59432 : _110698) (s : _110698 -> Prop) : (term457 _110698 s r _59432 _59433) = (term461 _110698 r _59433 _59432 s).
Proof. exact (TRANS (@lem4805449 _110698 r _59433 _59432 s) (@lem4805454 _110698 r _59433 _59432 s)). Qed.
Lemma lem4805473 {_110698 : Type'} (r : type1402 _110698) (_59433 : _110698) (_59432 : _110698) (s : _110698 -> Prop) : (term383 _110698 s r _59432 _59433) = (term461 _110698 r _59433 _59432 s).
Proof. exact (TRANS (@lem4805425 _110698 s r _59432 _59433) (@lem4805472 _110698 r _59433 _59432 s)). Qed.
Lemma lem4805474 {_110698 : Type'} (_59433 : _110698) (x : _110698) : (term375 _110698 _59433 x) = (term375 _110698 _59433 x).
Proof. exact (eq_refl (term375 _110698 _59433 x)). Qed.
Lemma lem4805475 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (_59433 : _110698) (_59432 : _110698) (s : _110698 -> Prop) : (term455 _110698 x s r _59432 _59433) = (term462 _110698 x r _59433 _59432 s).
Proof. exact (MK_COMB (@lem4805474 _110698 _59433 x) (@lem4805473 _110698 r _59433 _59432 s)). Qed.
Lemma lem4805479 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4805480 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59433 : _110698) (_59432 : _110698) (s : _110698 -> Prop) : (term462 _110698 x r _59433 _59432 s) = (term463 _110698 r x _59433 _59432 s).
Proof. exact (@lem4805479 (r _59432 _59433) (term22 _110698 _59433 x) (term464 _110698 _59433 _59432 s)). Qed.
Lemma lem4805494 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4805495 {_110698 : Type'} (_59433 : _110698) (x : _110698) (_59432 : _110698) (s : _110698 -> Prop) : (term465 _110698 x _59433 _59432 s) = (term466 _110698 _59433 x _59432 s).
Proof. exact (@lem4805494 (_59432 = _59433) (term22 _110698 _59433 x) (term331 _110698 _59432 s)). Qed.
Lemma lem4805515 {_110698 : Type'} (r : type1402 _110698) (_59432 : _110698) (_59433 : _110698) : (term433 _110698 r _59432 _59433) = (term433 _110698 r _59432 _59433).
Proof. exact (eq_refl (term433 _110698 r _59432 _59433)). Qed.
Lemma lem4805516 {_110698 : Type'} (r : type1402 _110698) (_59433 : _110698) (x : _110698) (_59432 : _110698) (s : _110698 -> Prop) : (term463 _110698 r x _59433 _59432 s) = (term467 _110698 r _59433 x _59432 s).
Proof. exact (MK_COMB (@lem4805515 _110698 r _59432 _59433) (@lem4805495 _110698 _59433 x _59432 s)). Qed.
Lemma lem4805527 {_110698 : Type'} (r : type1402 _110698) (_59433 : _110698) (x : _110698) (_59432 : _110698) (s : _110698 -> Prop) : (term462 _110698 x r _59433 _59432 s) = (term467 _110698 r _59433 x _59432 s).
Proof. exact (TRANS (@lem4805480 _110698 r x _59433 _59432 s) (@lem4805516 _110698 r _59433 x _59432 s)). Qed.
Lemma lem4805528 {_110698 : Type'} (r : type1402 _110698) (_59433 : _110698) (x : _110698) (_59432 : _110698) (s : _110698 -> Prop) : (term455 _110698 x s r _59432 _59433) = (term467 _110698 r _59433 x _59432 s).
Proof. exact (TRANS (@lem4805475 _110698 x r _59433 _59432 s) (@lem4805527 _110698 r _59433 x _59432 s)). Qed.
Lemma lem4805529 {_110698 : Type'} (r : type1402 _110698) (_59433 : _110698) (x : _110698) (_59432 : _110698) (s : _110698 -> Prop) : (term380 _110698 s x r _59432 _59433) = (term467 _110698 r _59433 x _59432 s).
Proof. exact (TRANS (@lem4805408 _110698 x s r _59432 _59433) (@lem4805528 _110698 r _59433 x _59432 s)). Qed.
Lemma lem4805530 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4805531 {_110698 : Type'} (r : type1402 _110698) (_59433 : _110698) (x : _110698) (_59432 : _110698) (s : _110698 -> Prop) : (term468 _110698 s x r _59432 _59433) = (term469 _110698 r _59433 x _59432 s).
Proof. exact (MK_COMB (@lem4805530) (@lem4805529 _110698 r _59433 x _59432 s)). Qed.
Lemma lem4805545 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4805546 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (_59432 : _110698) (_59433 : _110698) : (term351 _110698 s x _59432 _59433) = (term470 _110698 x s _59432 _59433).
Proof. exact (@lem4805545 (term22 _110698 _59433 x) (term331 _110698 _59432 s) (_59432 = _59433)). Qed.
Lemma lem4805562 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4805563 {_110698 : Type'} (_59433 : _110698) (_59432 : _110698) (s : _110698 -> Prop) : (term111 _110698 s _59432 _59433) = (term464 _110698 _59433 _59432 s).
Proof. exact (@lem4805562 (_59432 = _59433) (term331 _110698 _59432 s)). Qed.
Lemma lem4805571 {_110698 : Type'} (_59433 : _110698) (x : _110698) : (term375 _110698 _59433 x) = (term375 _110698 _59433 x).
Proof. exact (eq_refl (term375 _110698 _59433 x)). Qed.
Lemma lem4805572 {_110698 : Type'} (x : _110698) (_59433 : _110698) (_59432 : _110698) (s : _110698 -> Prop) : (term470 _110698 x s _59432 _59433) = (term465 _110698 x _59433 _59432 s).
Proof. exact (MK_COMB (@lem4805571 _110698 _59433 x) (@lem4805563 _110698 _59433 _59432 s)). Qed.
Lemma lem4805576 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4805577 {_110698 : Type'} (_59433 : _110698) (x : _110698) (_59432 : _110698) (s : _110698 -> Prop) : (term465 _110698 x _59433 _59432 s) = (term466 _110698 _59433 x _59432 s).
Proof. exact (@lem4805576 (_59432 = _59433) (term22 _110698 _59433 x) (term331 _110698 _59432 s)). Qed.
Lemma lem4805597 {_110698 : Type'} (_59433 : _110698) (x : _110698) (_59432 : _110698) (s : _110698 -> Prop) : (term470 _110698 x s _59432 _59433) = (term466 _110698 _59433 x _59432 s).
Proof. exact (TRANS (@lem4805572 _110698 x _59433 _59432 s) (@lem4805577 _110698 _59433 x _59432 s)). Qed.
Lemma lem4805598 {_110698 : Type'} (_59433 : _110698) (x : _110698) (_59432 : _110698) (s : _110698 -> Prop) : (term351 _110698 s x _59432 _59433) = (term466 _110698 _59433 x _59432 s).
Proof. exact (TRANS (@lem4805546 _110698 x s _59432 _59433) (@lem4805597 _110698 _59433 x _59432 s)). Qed.
Lemma lem4805599 {_110698 : Type'} (r : type1402 _110698) (_59432 : _110698) (_59433 : _110698) : (term433 _110698 r _59432 _59433) = (term433 _110698 r _59432 _59433).
Proof. exact (eq_refl (term433 _110698 r _59432 _59433)). Qed.
Lemma lem4805600 {_110698 : Type'} (r : type1402 _110698) (_59433 : _110698) (x : _110698) (_59432 : _110698) (s : _110698 -> Prop) : (term471 _110698 r s x _59432 _59433) = (term467 _110698 r _59433 x _59432 s).
Proof. exact (MK_COMB (@lem4805599 _110698 r _59432 _59433) (@lem4805598 _110698 _59433 x _59432 s)). Qed.
Lemma lem4805611 {_110698 : Type'} (r : type1402 _110698) (_59433 : _110698) (x : _110698) (_59432 : _110698) (s : _110698 -> Prop) : ((term380 _110698 s x r _59432 _59433) = (term471 _110698 r s x _59432 _59433)) = ((term467 _110698 r _59433 x _59432 s) = (term467 _110698 r _59433 x _59432 s)).
Proof. exact (MK_COMB (@lem4805531 _110698 r _59433 x _59432 s) (@lem4805600 _110698 r _59433 x _59432 s)). Qed.
Lemma lem4805613 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4805614 (x : Prop) : (x = x) = True.
Proof. exact (@lem4805613 Prop x). Qed.
Lemma lem4805615 {_110698 : Type'} (r : type1402 _110698) (_59433 : _110698) (x : _110698) (_59432 : _110698) (s : _110698 -> Prop) : ((term467 _110698 r _59433 x _59432 s) = (term467 _110698 r _59433 x _59432 s)) = True.
Proof. exact (@lem4805614 (term467 _110698 r _59433 x _59432 s)). Qed.
Lemma lem4805616 {_110698 : Type'} (r : type1402 _110698) (s : _110698 -> Prop) (x : _110698) (_59432 : _110698) (_59433 : _110698) : ((term380 _110698 s x r _59432 _59433) = (term471 _110698 r s x _59432 _59433)) = True.
Proof. exact (TRANS (@lem4805611 _110698 r _59433 x _59432 s) (@lem4805615 _110698 r _59433 x _59432 s)). Qed.
Lemma lem4805617 {_110698 : Type'} (r : type1402 _110698) (s : _110698 -> Prop) (x : _110698) (_59432 : _110698) (_59433 : _110698) : True = ((term380 _110698 s x r _59432 _59433) = (term471 _110698 r s x _59432 _59433)).
Proof. exact (SYM (@lem4805616 _110698 r s x _59432 _59433)). Qed.
Lemma lem4805618 {_110698 : Type'} (r : type1402 _110698) (s : _110698 -> Prop) (x : _110698) (_59432 : _110698) (_59433 : _110698) : (term380 _110698 s x r _59432 _59433) = (term471 _110698 r s x _59432 _59433).
Proof. exact (EQ_MP (@lem4805617 _110698 r s x _59432 _59433) (@lem0)). Qed.
Lemma lem4805619 {_110698 : Type'} (_59432 : _110698) (_59433 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term471 _110698 r s x _59432 _59433.
Proof. exact (EQ_MP (@lem4805618 _110698 r s x _59432 _59433) (@lem4804316 _110698 _59432 _59433 x s r y y' h1)). Qed.
Lemma lem4805621 (b : Prop) (a : Prop) : (a \/ b) = (term407 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4805622 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (r : type1402 _110698) (_59432 : _110698) (_59433 : _110698) : (term471 _110698 r s x _59432 _59433) = (term472 _110698 s x r _59432 _59433).
Proof. exact (@lem4805621 (term351 _110698 s x _59432 _59433) (r _59432 _59433)). Qed.
Lemma lem4805624 (a : Prop) (b : Prop) : (term410 a b) = (term411 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4805625 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (_59432 : _110698) (_59433 : _110698) : (term473 _110698 s x _59432 _59433) = (term474 _110698 s x _59432 _59433).
Proof. exact (@lem4805624 (term331 _110698 _59432 s) (term334 _110698 x _59432 _59433)). Qed.
Lemma lem4805627 (a : Prop) : (term62 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4805628 {_110698 : Type'} (_59432 : _110698) (s : _110698 -> Prop) : (term443 _110698 _59432 s) = (@IN _110698 _59432 s).
Proof. exact (@lem4805627 (@IN _110698 _59432 s)). Qed.
Lemma lem4805629 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4805630 {_110698 : Type'} (_59432 : _110698) (s : _110698 -> Prop) : (term444 _110698 _59432 s) = (term445 _110698 _59432 s).
Proof. exact (MK_COMB (@lem4805629) (@lem4805628 _110698 _59432 s)). Qed.
Lemma lem4805632 (a : Prop) (b : Prop) : (term410 a b) = (term411 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4805633 {_110698 : Type'} (x : _110698) (_59432 : _110698) (_59433 : _110698) : (term475 _110698 x _59432 _59433) = (term476 _110698 x _59432 _59433).
Proof. exact (@lem4805632 (term22 _110698 _59433 x) (_59432 = _59433)). Qed.
Lemma lem4805635 (a : Prop) : (term62 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4805636 {_110698 : Type'} (_59433 : _110698) (x : _110698) : (term74 _110698 _59433 x) = (_59433 = x).
Proof. exact (@lem4805635 (_59433 = x)). Qed.
Lemma lem4805637 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4805638 {_110698 : Type'} (_59433 : _110698) (x : _110698) : (term414 _110698 _59433 x) = (term415 _110698 _59433 x).
Proof. exact (MK_COMB (@lem4805637) (@lem4805636 _110698 _59433 x)). Qed.
Lemma lem4805639 {_110698 : Type'} (_59432 : _110698) (_59433 : _110698) : (term22 _110698 _59432 _59433) = (term22 _110698 _59432 _59433).
Proof. exact (eq_refl (term22 _110698 _59432 _59433)). Qed.
Lemma lem4805640 {_110698 : Type'} (x : _110698) (_59432 : _110698) (_59433 : _110698) : (term476 _110698 x _59432 _59433) = (term477 _110698 x _59432 _59433).
Proof. exact (MK_COMB (@lem4805638 _110698 _59433 x) (@lem4805639 _110698 _59432 _59433)). Qed.
Lemma lem4805641 {_110698 : Type'} (x : _110698) (_59432 : _110698) (_59433 : _110698) : (term475 _110698 x _59432 _59433) = (term477 _110698 x _59432 _59433).
Proof. exact (TRANS (@lem4805633 _110698 x _59432 _59433) (@lem4805640 _110698 x _59432 _59433)). Qed.
Lemma lem4805642 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (_59432 : _110698) (_59433 : _110698) : (term474 _110698 s x _59432 _59433) = (term478 _110698 s x _59432 _59433).
Proof. exact (MK_COMB (@lem4805630 _110698 _59432 s) (@lem4805641 _110698 x _59432 _59433)). Qed.
Lemma lem4805643 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (_59432 : _110698) (_59433 : _110698) : (term473 _110698 s x _59432 _59433) = (term478 _110698 s x _59432 _59433).
Proof. exact (TRANS (@lem4805625 _110698 s x _59432 _59433) (@lem4805642 _110698 s x _59432 _59433)). Qed.
Lemma lem4805644 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4805645 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (_59432 : _110698) (_59433 : _110698) : (term479 _110698 s x _59432 _59433) = (term480 _110698 s x _59432 _59433).
Proof. exact (MK_COMB (@lem4805644) (@lem4805643 _110698 s x _59432 _59433)). Qed.
Lemma lem4805646 {_110698 : Type'} (r : type1402 _110698) (_59432 : _110698) (_59433 : _110698) : (r _59432 _59433) = (r _59432 _59433).
Proof. exact (eq_refl (r _59432 _59433)). Qed.
Lemma lem4805647 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (r : type1402 _110698) (_59432 : _110698) (_59433 : _110698) : (term472 _110698 s x r _59432 _59433) = (term481 _110698 s x r _59432 _59433).
Proof. exact (MK_COMB (@lem4805645 _110698 s x _59432 _59433) (@lem4805646 _110698 r _59432 _59433)). Qed.
Lemma lem4805648 {_110698 : Type'} (s : _110698 -> Prop) (x : _110698) (r : type1402 _110698) (_59432 : _110698) (_59433 : _110698) : (term471 _110698 r s x _59432 _59433) = (term481 _110698 s x r _59432 _59433).
Proof. exact (TRANS (@lem4805622 _110698 s x r _59432 _59433) (@lem4805647 _110698 s x r _59432 _59433)). Qed.
Lemma lem4805650 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term118 _110698 s r y x) : term420 _110698 y x.
Proof. exact (conj (@lem4805394 _110698 x) (@lem4805401 _110698 s r y x h1)). Qed.
Lemma lem4805651 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term118 _110698 s r y x) : term482 _110698 s y x.
Proof. exact (conj (@lem4805386 _110698 s r y x h1) (@lem4805650 _110698 s r y x h1)). Qed.
Lemma lem4805653 {_110698 : Type'} (_59432 : _110698) (_59433 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term481 _110698 s x r _59432 _59433.
Proof. exact (EQ_MP (@lem4805648 _110698 s x r _59432 _59433) (@lem4805619 _110698 _59432 _59433 x s r y y' h1)). Qed.
Lemma lem4805654 {_110698 : Type'} (_59432 : _110698) (_59433 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term481 _110698 s x r _59432 _59433.
Proof. exact (@lem4805653 _110698 _59432 _59433 x s r y y' h1). Qed.
Lemma lem4805655 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term483 _110698 s r y x.
Proof. exact (@lem4805654 _110698 y x x s r y y' h1). Qed.
Lemma lem4805658 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term247 _110698 x s r y y') (h2 : term118 _110698 s r y x) : r y x.
Proof. exact (@lem4805655 _110698 x s r y y' h1 (@lem4805651 _110698 s r y x h2)). Qed.
Lemma lem4805659 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term247 _110698 x s r y y') (h2 : term118 _110698 s r y x) : term452 _110698 r y x.
Proof. exact (fun h0 : term359 _110698 r y x => @lem4805658 _110698 y' s r y x h1 h2). Qed.
Lemma lem4805661 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4805662 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) : (term452 _110698 r y x) = (r y x).
Proof. exact (@lem4805661 (r y x)). Qed.
Lemma lem4805663 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term247 _110698 x s r y y') (h2 : term118 _110698 s r y x) : r y x.
Proof. exact (EQ_MP (@lem4805662 _110698 r y x) (@lem4805659 _110698 y' s r y x h1 h2)). Qed.
Lemma lem4805666 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4805668 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) : (term359 _110698 r y x) = (term453 _110698 r y x).
Proof. exact (@lem4805666 (r y x)). Qed.
Lemma lem4805671 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term359 _110698 r y x) : term453 _110698 r y x.
Proof. exact (EQ_MP (@lem4805668 _110698 r y x) (@lem4804244 _110698 r y x h1)). Qed.
Lemma lem4805674 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term359 _110698 r y x) (h2 : term247 _110698 x s r y y') (h3 : term118 _110698 s r y x) : False.
Proof. exact (@lem4805671 _110698 r y x h1 (@lem4805663 _110698 y' s r y x h2 h3)). Qed.
Lemma lem4805675 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term359 _110698 r y x) (h2 : term247 _110698 x s r y y') (h3 : term118 _110698 s r y x) : term454.
Proof. exact (fun h0 : ~ False => @lem4805674 _110698 y' s r y x h1 h2 h3). Qed.
Lemma lem4805677 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4805678 : term454 = False.
Proof. exact (@lem4805677 False). Qed.
Lemma lem4805679 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term359 _110698 r y x) (h2 : term247 _110698 x s r y y') (h3 : term118 _110698 s r y x) : False.
Proof. exact (EQ_MP (@lem4805678) (@lem4805675 _110698 y' s r y x h1 h2 h3)). Qed.
Lemma lem4805723 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term142 _110698 s r y y') : @IN _110698 y s.
Proof. exact (proj1 (@lem4803494 _110698 s r y y' h1)). Qed.
Lemma lem4805724 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term142 _110698 s r y y') : term404 _110698 y s.
Proof. exact (fun h0 : term331 _110698 y s => @lem4805723 _110698 s r y y' h1). Qed.
Lemma lem4805726 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4805727 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) : (term404 _110698 y s) = (@IN _110698 y s).
Proof. exact (@lem4805726 (@IN _110698 y s)). Qed.
Lemma lem4805728 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term142 _110698 s r y y') : @IN _110698 y s.
Proof. exact (EQ_MP (@lem4805727 _110698 y s) (@lem4805724 _110698 s r y y' h1)). Qed.
Lemma lem4805730 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term142 _110698 s r y y') : @IN _110698 y' s.
Proof. exact (proj1 (@lem4803495 _110698 s r y y' h1)). Qed.
Lemma lem4805731 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term142 _110698 s r y y') : term404 _110698 y' s.
Proof. exact (fun h0 : term331 _110698 y' s => @lem4805730 _110698 s r y y' h1). Qed.
Lemma lem4805733 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4805734 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) : (term404 _110698 y' s) = (@IN _110698 y' s).
Proof. exact (@lem4805733 (@IN _110698 y' s)). Qed.
Lemma lem4805735 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term142 _110698 s r y y') : @IN _110698 y' s.
Proof. exact (EQ_MP (@lem4805734 _110698 y' s) (@lem4805731 _110698 s r y y' h1)). Qed.
Lemma lem4805737 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term142 _110698 s r y y') : term359 _110698 r y y'.
Proof. exact (proj2 (@lem4803486 _110698 s r y y' h1)). Qed.
Lemma lem4805738 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term142 _110698 s r y y') : term484 _110698 r y y'.
Proof. exact (fun h0 : r y y' => @lem4805737 _110698 s r y y' h1). Qed.
Lemma lem4805740 (p : Prop) : (term406 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4805741 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (y' : _110698) : (term484 _110698 r y y') = (term359 _110698 r y y').
Proof. exact (@lem4805740 (r y y')). Qed.
Lemma lem4805742 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term142 _110698 s r y y') : term359 _110698 r y y'.
Proof. exact (EQ_MP (@lem4805741 _110698 r y y') (@lem4805738 _110698 s r y y' h1)). Qed.
Lemma lem4805758 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4805759 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) : (term374 _110698 s r _59434 _59435) = (term422 _110698 s r _59434 _59435).
Proof. exact (@lem4805758 (_59434 = _59435) (term331 _110698 _59435 s) (r _59434 _59435)). Qed.
Lemma lem4805775 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4805776 {_110698 : Type'} (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) (s : _110698 -> Prop) : (term423 _110698 s r _59434 _59435) = (term424 _110698 r _59434 _59435 s).
Proof. exact (@lem4805775 (r _59434 _59435) (term331 _110698 _59435 s)). Qed.
Lemma lem4805782 {_110698 : Type'} (_59434 : _110698) (_59435 : _110698) : (term425 _110698 _59434 _59435) = (term425 _110698 _59434 _59435).
Proof. exact (eq_refl (term425 _110698 _59434 _59435)). Qed.
Lemma lem4805783 {_110698 : Type'} (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) (s : _110698 -> Prop) : (term422 _110698 s r _59434 _59435) = (term426 _110698 r _59434 _59435 s).
Proof. exact (MK_COMB (@lem4805782 _110698 _59434 _59435) (@lem4805776 _110698 r _59434 _59435 s)). Qed.
Lemma lem4805787 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4805788 {_110698 : Type'} (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) (s : _110698 -> Prop) : (term426 _110698 r _59434 _59435 s) = (term427 _110698 r _59434 _59435 s).
Proof. exact (@lem4805787 (r _59434 _59435) (_59434 = _59435) (term331 _110698 _59435 s)). Qed.
Lemma lem4805806 {_110698 : Type'} (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) (s : _110698 -> Prop) : (term422 _110698 s r _59434 _59435) = (term427 _110698 r _59434 _59435 s).
Proof. exact (TRANS (@lem4805783 _110698 r _59434 _59435 s) (@lem4805788 _110698 r _59434 _59435 s)). Qed.
Lemma lem4805807 {_110698 : Type'} (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) (s : _110698 -> Prop) : (term374 _110698 s r _59434 _59435) = (term427 _110698 r _59434 _59435 s).
Proof. exact (TRANS (@lem4805759 _110698 s r _59434 _59435) (@lem4805806 _110698 r _59434 _59435 s)). Qed.
Lemma lem4805808 {_110698 : Type'} (_59434 : _110698) (s : _110698 -> Prop) : (term109 _110698 _59434 s) = (term109 _110698 _59434 s).
Proof. exact (eq_refl (term109 _110698 _59434 s)). Qed.
Lemma lem4805809 {_110698 : Type'} (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) (s : _110698 -> Prop) : (term382 _110698 s r _59434 _59435) = (term485 _110698 r _59434 _59435 s).
Proof. exact (MK_COMB (@lem4805808 _110698 _59434 s) (@lem4805807 _110698 r _59434 _59435 s)). Qed.
Lemma lem4805813 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4805814 {_110698 : Type'} (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) (s : _110698 -> Prop) : (term485 _110698 r _59434 _59435 s) = (term486 _110698 r _59434 _59435 s).
Proof. exact (@lem4805813 (r _59434 _59435) (term331 _110698 _59434 s) (term430 _110698 _59434 _59435 s)). Qed.
Lemma lem4805828 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4805829 {_110698 : Type'} (_59434 : _110698) (_59435 : _110698) (s : _110698 -> Prop) : (term487 _110698 _59434 _59435 s) = (term488 _110698 _59434 _59435 s).
Proof. exact (@lem4805828 (_59434 = _59435) (term331 _110698 _59434 s) (term331 _110698 _59435 s)). Qed.
Lemma lem4805847 {_110698 : Type'} (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) : (term433 _110698 r _59434 _59435) = (term433 _110698 r _59434 _59435).
Proof. exact (eq_refl (term433 _110698 r _59434 _59435)). Qed.
Lemma lem4805848 {_110698 : Type'} (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) (s : _110698 -> Prop) : (term486 _110698 r _59434 _59435 s) = (term489 _110698 r _59434 _59435 s).
Proof. exact (MK_COMB (@lem4805847 _110698 r _59434 _59435) (@lem4805829 _110698 _59434 _59435 s)). Qed.
Lemma lem4805859 {_110698 : Type'} (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) (s : _110698 -> Prop) : (term485 _110698 r _59434 _59435 s) = (term489 _110698 r _59434 _59435 s).
Proof. exact (TRANS (@lem4805814 _110698 r _59434 _59435 s) (@lem4805848 _110698 r _59434 _59435 s)). Qed.
Lemma lem4805860 {_110698 : Type'} (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) (s : _110698 -> Prop) : (term382 _110698 s r _59434 _59435) = (term489 _110698 r _59434 _59435 s).
Proof. exact (TRANS (@lem4805809 _110698 r _59434 _59435 s) (@lem4805859 _110698 r _59434 _59435 s)). Qed.
Lemma lem4805861 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4805862 {_110698 : Type'} (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) (s : _110698 -> Prop) : (term490 _110698 s r _59434 _59435) = (term491 _110698 r _59434 _59435 s).
Proof. exact (MK_COMB (@lem4805861) (@lem4805860 _110698 r _59434 _59435 s)). Qed.
Lemma lem4805888 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4805889 {_110698 : Type'} (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) (s : _110698 -> Prop) : (term423 _110698 s r _59434 _59435) = (term424 _110698 r _59434 _59435 s).
Proof. exact (@lem4805888 (r _59434 _59435) (term331 _110698 _59435 s)). Qed.
Lemma lem4805895 {_110698 : Type'} (_59434 : _110698) (s : _110698 -> Prop) : (term109 _110698 _59434 s) = (term109 _110698 _59434 s).
Proof. exact (eq_refl (term109 _110698 _59434 s)). Qed.
Lemma lem4805896 {_110698 : Type'} (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) (s : _110698 -> Prop) : (term492 _110698 s r _59434 _59435) = (term493 _110698 r _59434 _59435 s).
Proof. exact (MK_COMB (@lem4805895 _110698 _59434 s) (@lem4805889 _110698 r _59434 _59435 s)). Qed.
Lemma lem4805900 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4805901 {_110698 : Type'} (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) (s : _110698 -> Prop) : (term493 _110698 r _59434 _59435 s) = (term494 _110698 r _59434 _59435 s).
Proof. exact (@lem4805900 (r _59434 _59435) (term331 _110698 _59434 s) (term331 _110698 _59435 s)). Qed.
Lemma lem4805917 {_110698 : Type'} (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) (s : _110698 -> Prop) : (term492 _110698 s r _59434 _59435) = (term494 _110698 r _59434 _59435 s).
Proof. exact (TRANS (@lem4805896 _110698 r _59434 _59435 s) (@lem4805901 _110698 r _59434 _59435 s)). Qed.
Lemma lem4805918 {_110698 : Type'} (_59434 : _110698) (_59435 : _110698) : (term425 _110698 _59434 _59435) = (term425 _110698 _59434 _59435).
Proof. exact (eq_refl (term425 _110698 _59434 _59435)). Qed.
Lemma lem4805919 {_110698 : Type'} (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) (s : _110698 -> Prop) : (term495 _110698 s r _59434 _59435) = (term496 _110698 r _59434 _59435 s).
Proof. exact (MK_COMB (@lem4805918 _110698 _59434 _59435) (@lem4805917 _110698 r _59434 _59435 s)). Qed.
Lemma lem4805923 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4805924 {_110698 : Type'} (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) (s : _110698 -> Prop) : (term496 _110698 r _59434 _59435 s) = (term489 _110698 r _59434 _59435 s).
Proof. exact (@lem4805923 (r _59434 _59435) (_59434 = _59435) (term497 _110698 _59434 _59435 s)). Qed.
Lemma lem4805952 {_110698 : Type'} (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) (s : _110698 -> Prop) : (term495 _110698 s r _59434 _59435) = (term489 _110698 r _59434 _59435 s).
Proof. exact (TRANS (@lem4805919 _110698 r _59434 _59435 s) (@lem4805924 _110698 r _59434 _59435 s)). Qed.
Lemma lem4805953 {_110698 : Type'} (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) (s : _110698 -> Prop) : ((term382 _110698 s r _59434 _59435) = (term495 _110698 s r _59434 _59435)) = ((term489 _110698 r _59434 _59435 s) = (term489 _110698 r _59434 _59435 s)).
Proof. exact (MK_COMB (@lem4805862 _110698 r _59434 _59435 s) (@lem4805952 _110698 r _59434 _59435 s)). Qed.
Lemma lem4805955 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4805956 (x : Prop) : (x = x) = True.
Proof. exact (@lem4805955 Prop x). Qed.
Lemma lem4805957 {_110698 : Type'} (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) (s : _110698 -> Prop) : ((term489 _110698 r _59434 _59435 s) = (term489 _110698 r _59434 _59435 s)) = True.
Proof. exact (@lem4805956 (term489 _110698 r _59434 _59435 s)). Qed.
Lemma lem4805958 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) : ((term382 _110698 s r _59434 _59435) = (term495 _110698 s r _59434 _59435)) = True.
Proof. exact (TRANS (@lem4805953 _110698 r _59434 _59435 s) (@lem4805957 _110698 r _59434 _59435 s)). Qed.
Lemma lem4805959 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) : True = ((term382 _110698 s r _59434 _59435) = (term495 _110698 s r _59434 _59435)).
Proof. exact (SYM (@lem4805958 _110698 s r _59434 _59435)). Qed.
Lemma lem4805960 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) : (term382 _110698 s r _59434 _59435) = (term495 _110698 s r _59434 _59435).
Proof. exact (EQ_MP (@lem4805959 _110698 s r _59434 _59435) (@lem0)). Qed.
Lemma lem4805961 {_110698 : Type'} (_59434 : _110698) (_59435 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term495 _110698 s r _59434 _59435.
Proof. exact (EQ_MP (@lem4805960 _110698 s r _59434 _59435) (@lem4804360 _110698 _59434 _59435 x s r y y' h1)). Qed.
Lemma lem4805963 (b : Prop) (a : Prop) : (a \/ b) = (term407 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4805964 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) : (term495 _110698 s r _59434 _59435) = (term498 _110698 s r _59434 _59435).
Proof. exact (@lem4805963 (term492 _110698 s r _59434 _59435) (_59434 = _59435)). Qed.
Lemma lem4805966 (a : Prop) (b : Prop) : (term410 a b) = (term411 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4805967 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) : (term499 _110698 s r _59434 _59435) = (term500 _110698 s r _59434 _59435).
Proof. exact (@lem4805966 (term331 _110698 _59434 s) (term423 _110698 s r _59434 _59435)). Qed.
Lemma lem4805969 (a : Prop) : (term62 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4805970 {_110698 : Type'} (_59434 : _110698) (s : _110698 -> Prop) : (term443 _110698 _59434 s) = (@IN _110698 _59434 s).
Proof. exact (@lem4805969 (@IN _110698 _59434 s)). Qed.
Lemma lem4805971 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4805972 {_110698 : Type'} (_59434 : _110698) (s : _110698 -> Prop) : (term444 _110698 _59434 s) = (term445 _110698 _59434 s).
Proof. exact (MK_COMB (@lem4805971) (@lem4805970 _110698 _59434 s)). Qed.
Lemma lem4805974 (a : Prop) (b : Prop) : (term410 a b) = (term411 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4805975 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) : (term501 _110698 s r _59434 _59435) = (term502 _110698 s r _59434 _59435).
Proof. exact (@lem4805974 (term331 _110698 _59435 s) (r _59434 _59435)). Qed.
Lemma lem4805977 (a : Prop) : (term62 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4805978 {_110698 : Type'} (_59435 : _110698) (s : _110698 -> Prop) : (term443 _110698 _59435 s) = (@IN _110698 _59435 s).
Proof. exact (@lem4805977 (@IN _110698 _59435 s)). Qed.
Lemma lem4805979 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4805980 {_110698 : Type'} (_59435 : _110698) (s : _110698 -> Prop) : (term444 _110698 _59435 s) = (term445 _110698 _59435 s).
Proof. exact (MK_COMB (@lem4805979) (@lem4805978 _110698 _59435 s)). Qed.
Lemma lem4805981 {_110698 : Type'} (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) : (term359 _110698 r _59434 _59435) = (term359 _110698 r _59434 _59435).
Proof. exact (eq_refl (term359 _110698 r _59434 _59435)). Qed.
Lemma lem4805982 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) : (term502 _110698 s r _59434 _59435) = (term503 _110698 s r _59434 _59435).
Proof. exact (MK_COMB (@lem4805980 _110698 _59435 s) (@lem4805981 _110698 r _59434 _59435)). Qed.
Lemma lem4805983 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) : (term501 _110698 s r _59434 _59435) = (term503 _110698 s r _59434 _59435).
Proof. exact (TRANS (@lem4805975 _110698 s r _59434 _59435) (@lem4805982 _110698 s r _59434 _59435)). Qed.
Lemma lem4805984 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) : (term500 _110698 s r _59434 _59435) = (term504 _110698 s r _59434 _59435).
Proof. exact (MK_COMB (@lem4805972 _110698 _59434 s) (@lem4805983 _110698 s r _59434 _59435)). Qed.
Lemma lem4805985 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) : (term499 _110698 s r _59434 _59435) = (term504 _110698 s r _59434 _59435).
Proof. exact (TRANS (@lem4805967 _110698 s r _59434 _59435) (@lem4805984 _110698 s r _59434 _59435)). Qed.
Lemma lem4805986 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4805987 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) : (term505 _110698 s r _59434 _59435) = (term506 _110698 s r _59434 _59435).
Proof. exact (MK_COMB (@lem4805986) (@lem4805985 _110698 s r _59434 _59435)). Qed.
Lemma lem4805988 {_110698 : Type'} (_59434 : _110698) (_59435 : _110698) : (_59434 = _59435) = (_59434 = _59435).
Proof. exact (eq_refl (_59434 = _59435)). Qed.
Lemma lem4805989 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) : (term498 _110698 s r _59434 _59435) = (term507 _110698 s r _59434 _59435).
Proof. exact (MK_COMB (@lem4805987 _110698 s r _59434 _59435) (@lem4805988 _110698 _59434 _59435)). Qed.
Lemma lem4805990 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59434 : _110698) (_59435 : _110698) : (term495 _110698 s r _59434 _59435) = (term507 _110698 s r _59434 _59435).
Proof. exact (TRANS (@lem4805964 _110698 s r _59434 _59435) (@lem4805989 _110698 s r _59434 _59435)). Qed.
Lemma lem4805992 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term142 _110698 s r y y') : term503 _110698 s r y y'.
Proof. exact (conj (@lem4805735 _110698 s r y y' h1) (@lem4805742 _110698 s r y y' h1)). Qed.
Lemma lem4805993 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term142 _110698 s r y y') : term504 _110698 s r y y'.
Proof. exact (conj (@lem4805728 _110698 s r y y' h1) (@lem4805992 _110698 s r y y' h1)). Qed.
Lemma lem4805995 {_110698 : Type'} (_59434 : _110698) (_59435 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term507 _110698 s r _59434 _59435.
Proof. exact (EQ_MP (@lem4805990 _110698 s r _59434 _59435) (@lem4805961 _110698 _59434 _59435 x s r y y' h1)). Qed.
Lemma lem4805996 {_110698 : Type'} (_59434 : _110698) (_59435 : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term507 _110698 s r _59434 _59435.
Proof. exact (@lem4805995 _110698 _59434 _59435 x s r y y' h1). Qed.
Lemma lem4805997 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : term507 _110698 s r y y'.
Proof. exact (@lem4805996 _110698 y y' x s r y y' h1). Qed.
Lemma lem4806000 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') (h2 : term142 _110698 s r y y') : y = y'.
Proof. exact (@lem4805997 _110698 x s r y y' h1 (@lem4805993 _110698 s r y y' h2)). Qed.
Lemma lem4806001 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') (h2 : term142 _110698 s r y y') : term508 _110698 y y'.
Proof. exact (fun h0 : term22 _110698 y y' => @lem4806000 _110698 x s r y y' h1 h2). Qed.
Lemma lem4806003 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4806004 {_110698 : Type'} (y : _110698) (y' : _110698) : (term508 _110698 y y') = (y = y').
Proof. exact (@lem4806003 (y = y')). Qed.
Lemma lem4806005 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') (h2 : term142 _110698 s r y y') : y = y'.
Proof. exact (EQ_MP (@lem4806004 _110698 y y') (@lem4806001 _110698 x s r y y' h1 h2)). Qed.
Lemma lem4806008 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4806010 {_110698 : Type'} (y : _110698) (y' : _110698) : (term22 _110698 y y') = (term509 _110698 y y').
Proof. exact (@lem4806008 (y = y')). Qed.
Lemma lem4806013 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term142 _110698 s r y y') : term509 _110698 y y'.
Proof. exact (EQ_MP (@lem4806010 _110698 y y') (@lem4804324 _110698 s r y y' h1)). Qed.
Lemma lem4806016 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') (h2 : term142 _110698 s r y y') : False.
Proof. exact (@lem4806013 _110698 s r y y' h2 (@lem4806005 _110698 x s r y y' h1 h2)). Qed.
Lemma lem4806017 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') (h2 : term142 _110698 s r y y') : term454.
Proof. exact (fun h0 : ~ False => @lem4806016 _110698 x s r y y' h1 h2). Qed.
Lemma lem4806019 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4806020 : term454 = False.
Proof. exact (@lem4806019 False). Qed.
Lemma lem4806021 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') (h2 : term142 _110698 s r y y') : False.
Proof. exact (EQ_MP (@lem4806020) (@lem4806017 _110698 x s r y y' h1 h2)). Qed.
Lemma lem4806065 {_110698 : Type'} (x : _110698) : x = x.
Proof. exact (@lem21386 _110698 x). Qed.
Lemma lem4806066 {_110698 : Type'} (x : _110698) : x = x.
Proof. exact (@lem4806065 _110698 x). Qed.
Lemma lem4806067 {_110698 : Type'} (x : _110698) : term402 _110698 x.
Proof. exact (fun h0 : term392 _110698 x => @lem4806066 _110698 x). Qed.
Lemma lem4806069 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4806070 {_110698 : Type'} (x : _110698) : (term402 _110698 x) = (x = x).
Proof. exact (@lem4806069 (x = x)). Qed.
Lemma lem4806071 {_110698 : Type'} (x : _110698) : x = x.
Proof. exact (EQ_MP (@lem4806070 _110698 x) (@lem4806067 _110698 x)). Qed.
Lemma lem4806074 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4806076 {_110698 : Type'} (x : _110698) : (term392 _110698 x) = (term510 _110698 x).
Proof. exact (@lem4806074 (x = x)). Qed.
Lemma lem4806079 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : y' = x) : term510 _110698 x.
Proof. exact (EQ_MP (@lem4806076 _110698 x) (@lem4804746 _110698 s r y y' x h1 h2 h3)). Qed.
Lemma lem4806082 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : y' = x) : False.
Proof. exact (@lem4806079 _110698 s r y y' x h1 h2 h3 (@lem4806071 _110698 x)). Qed.
Lemma lem4806083 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : y' = x) : term454.
Proof. exact (fun h0 : ~ False => @lem4806082 _110698 s r y y' x h1 h2 h3). Qed.
Lemma lem4806085 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4806086 : term454 = False.
Proof. exact (@lem4806085 False). Qed.
Lemma lem4806131 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) (h1 : @IN _110698 y s) : @IN _110698 y s.
Proof. exact (h1). Qed.
Lemma lem4806132 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) (h1 : @IN _110698 y s) : term404 _110698 y s.
Proof. exact (fun h0 : term331 _110698 y s => @lem4806131 _110698 y s h1). Qed.
Lemma lem4806134 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4806135 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) : (term404 _110698 y s) = (@IN _110698 y s).
Proof. exact (@lem4806134 (@IN _110698 y s)). Qed.
Lemma lem4806136 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) (h1 : @IN _110698 y s) : @IN _110698 y s.
Proof. exact (EQ_MP (@lem4806135 _110698 y s) (@lem4806132 _110698 y s h1)). Qed.
Lemma lem4806138 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) : term359 _110698 r y x.
Proof. exact (EQ_MP (@lem4804814 _110698 r y y' x h2) (@lem4804466 _110698 y y' x s r h1)). Qed.
Lemma lem4806139 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) : term484 _110698 r y x.
Proof. exact (fun h0 : r y x => @lem4806138 _110698 y s r y' x h1 h2). Qed.
Lemma lem4806141 (p : Prop) : (term406 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4806142 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) : (term484 _110698 r y x) = (term359 _110698 r y x).
Proof. exact (@lem4806141 (r y x)). Qed.
Lemma lem4806143 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) : term359 _110698 r y x.
Proof. exact (EQ_MP (@lem4806142 _110698 r y x) (@lem4806139 _110698 y s r y' x h1 h2)). Qed.
Lemma lem4806149 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4806150 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59439 : _110698) (x : _110698) : (term383 _110698 s r _59439 x) = (term457 _110698 s r _59439 x).
Proof. exact (@lem4806149 (_59439 = x) (term331 _110698 _59439 s) (r _59439 x)). Qed.
Lemma lem4806166 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4806167 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59439 : _110698) (s : _110698 -> Prop) : (term458 _110698 s r _59439 x) = (term459 _110698 r x _59439 s).
Proof. exact (@lem4806166 (r _59439 x) (term331 _110698 _59439 s)). Qed.
Lemma lem4806173 {_110698 : Type'} (_59439 : _110698) (x : _110698) : (term425 _110698 _59439 x) = (term425 _110698 _59439 x).
Proof. exact (eq_refl (term425 _110698 _59439 x)). Qed.
Lemma lem4806174 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59439 : _110698) (s : _110698 -> Prop) : (term457 _110698 s r _59439 x) = (term460 _110698 r x _59439 s).
Proof. exact (MK_COMB (@lem4806173 _110698 _59439 x) (@lem4806167 _110698 r x _59439 s)). Qed.
Lemma lem4806178 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4806179 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59439 : _110698) (s : _110698 -> Prop) : (term460 _110698 r x _59439 s) = (term461 _110698 r x _59439 s).
Proof. exact (@lem4806178 (r _59439 x) (_59439 = x) (term331 _110698 _59439 s)). Qed.
Lemma lem4806197 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59439 : _110698) (s : _110698 -> Prop) : (term457 _110698 s r _59439 x) = (term461 _110698 r x _59439 s).
Proof. exact (TRANS (@lem4806174 _110698 r x _59439 s) (@lem4806179 _110698 r x _59439 s)). Qed.
Lemma lem4806198 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59439 : _110698) (s : _110698 -> Prop) : (term383 _110698 s r _59439 x) = (term461 _110698 r x _59439 s).
Proof. exact (TRANS (@lem4806150 _110698 s r _59439 x) (@lem4806197 _110698 r x _59439 s)). Qed.
Lemma lem4806199 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4806200 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59439 : _110698) (s : _110698 -> Prop) : (term511 _110698 s r _59439 x) = (term512 _110698 r x _59439 s).
Proof. exact (MK_COMB (@lem4806199) (@lem4806198 _110698 r x _59439 s)). Qed.
Lemma lem4806216 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4806217 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59439 : _110698) (s : _110698 -> Prop) : (term458 _110698 s r _59439 x) = (term459 _110698 r x _59439 s).
Proof. exact (@lem4806216 (r _59439 x) (term331 _110698 _59439 s)). Qed.
Lemma lem4806223 {_110698 : Type'} (_59439 : _110698) (x : _110698) : (term425 _110698 _59439 x) = (term425 _110698 _59439 x).
Proof. exact (eq_refl (term425 _110698 _59439 x)). Qed.
Lemma lem4806224 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59439 : _110698) (s : _110698 -> Prop) : (term457 _110698 s r _59439 x) = (term460 _110698 r x _59439 s).
Proof. exact (MK_COMB (@lem4806223 _110698 _59439 x) (@lem4806217 _110698 r x _59439 s)). Qed.
Lemma lem4806228 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4806229 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59439 : _110698) (s : _110698 -> Prop) : (term460 _110698 r x _59439 s) = (term461 _110698 r x _59439 s).
Proof. exact (@lem4806228 (r _59439 x) (_59439 = x) (term331 _110698 _59439 s)). Qed.
Lemma lem4806247 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59439 : _110698) (s : _110698 -> Prop) : (term457 _110698 s r _59439 x) = (term461 _110698 r x _59439 s).
Proof. exact (TRANS (@lem4806224 _110698 r x _59439 s) (@lem4806229 _110698 r x _59439 s)). Qed.
Lemma lem4806248 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59439 : _110698) (s : _110698 -> Prop) : ((term383 _110698 s r _59439 x) = (term457 _110698 s r _59439 x)) = ((term461 _110698 r x _59439 s) = (term461 _110698 r x _59439 s)).
Proof. exact (MK_COMB (@lem4806200 _110698 r x _59439 s) (@lem4806247 _110698 r x _59439 s)). Qed.
Lemma lem4806250 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4806251 (x : Prop) : (x = x) = True.
Proof. exact (@lem4806250 Prop x). Qed.
Lemma lem4806252 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59439 : _110698) (s : _110698 -> Prop) : ((term461 _110698 r x _59439 s) = (term461 _110698 r x _59439 s)) = True.
Proof. exact (@lem4806251 (term461 _110698 r x _59439 s)). Qed.
Lemma lem4806253 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59439 : _110698) (x : _110698) : ((term383 _110698 s r _59439 x) = (term457 _110698 s r _59439 x)) = True.
Proof. exact (TRANS (@lem4806248 _110698 r x _59439 s) (@lem4806252 _110698 r x _59439 s)). Qed.
Lemma lem4806254 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59439 : _110698) (x : _110698) : True = ((term383 _110698 s r _59439 x) = (term457 _110698 s r _59439 x)).
Proof. exact (SYM (@lem4806253 _110698 s r _59439 x)). Qed.
Lemma lem4806255 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59439 : _110698) (x : _110698) : (term383 _110698 s r _59439 x) = (term457 _110698 s r _59439 x).
Proof. exact (EQ_MP (@lem4806254 _110698 s r _59439 x) (@lem0)). Qed.
Lemma lem4806256 {_110698 : Type'} (_59439 : _110698) (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term457 _110698 s r _59439 x.
Proof. exact (EQ_MP (@lem4806255 _110698 s r _59439 x) (@lem4804870 _110698 _59439 y y' x s r h1)). Qed.
Lemma lem4806258 (b : Prop) (a : Prop) : (a \/ b) = (term407 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4806259 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59439 : _110698) (x : _110698) : (term457 _110698 s r _59439 x) = (term513 _110698 s r _59439 x).
Proof. exact (@lem4806258 (term458 _110698 s r _59439 x) (_59439 = x)). Qed.
Lemma lem4806261 (a : Prop) (b : Prop) : (term410 a b) = (term411 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4806262 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59439 : _110698) (x : _110698) : (term514 _110698 s r _59439 x) = (term515 _110698 s r _59439 x).
Proof. exact (@lem4806261 (term331 _110698 _59439 s) (r _59439 x)). Qed.
Lemma lem4806264 (a : Prop) : (term62 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4806265 {_110698 : Type'} (_59439 : _110698) (s : _110698 -> Prop) : (term443 _110698 _59439 s) = (@IN _110698 _59439 s).
Proof. exact (@lem4806264 (@IN _110698 _59439 s)). Qed.
Lemma lem4806266 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4806267 {_110698 : Type'} (_59439 : _110698) (s : _110698 -> Prop) : (term444 _110698 _59439 s) = (term445 _110698 _59439 s).
Proof. exact (MK_COMB (@lem4806266) (@lem4806265 _110698 _59439 s)). Qed.
Lemma lem4806268 {_110698 : Type'} (r : type1402 _110698) (_59439 : _110698) (x : _110698) : (term359 _110698 r _59439 x) = (term359 _110698 r _59439 x).
Proof. exact (eq_refl (term359 _110698 r _59439 x)). Qed.
Lemma lem4806269 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59439 : _110698) (x : _110698) : (term515 _110698 s r _59439 x) = (term516 _110698 s r _59439 x).
Proof. exact (MK_COMB (@lem4806267 _110698 _59439 s) (@lem4806268 _110698 r _59439 x)). Qed.
Lemma lem4806270 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59439 : _110698) (x : _110698) : (term514 _110698 s r _59439 x) = (term516 _110698 s r _59439 x).
Proof. exact (TRANS (@lem4806262 _110698 s r _59439 x) (@lem4806269 _110698 s r _59439 x)). Qed.
Lemma lem4806271 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4806272 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59439 : _110698) (x : _110698) : (term517 _110698 s r _59439 x) = (term518 _110698 s r _59439 x).
Proof. exact (MK_COMB (@lem4806271) (@lem4806270 _110698 s r _59439 x)). Qed.
Lemma lem4806273 {_110698 : Type'} (_59439 : _110698) (x : _110698) : (_59439 = x) = (_59439 = x).
Proof. exact (eq_refl (_59439 = x)). Qed.
Lemma lem4806274 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59439 : _110698) (x : _110698) : (term513 _110698 s r _59439 x) = (term519 _110698 s r _59439 x).
Proof. exact (MK_COMB (@lem4806272 _110698 s r _59439 x) (@lem4806273 _110698 _59439 x)). Qed.
Lemma lem4806275 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59439 : _110698) (x : _110698) : (term457 _110698 s r _59439 x) = (term519 _110698 s r _59439 x).
Proof. exact (TRANS (@lem4806259 _110698 s r _59439 x) (@lem4806274 _110698 s r _59439 x)). Qed.
Lemma lem4806277 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (x : _110698) (y : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) (h3 : @IN _110698 y s) : term516 _110698 s r y x.
Proof. exact (conj (@lem4806136 _110698 y s h3) (@lem4806143 _110698 y s r y' x h1 h2)). Qed.
Lemma lem4806279 {_110698 : Type'} (_59439 : _110698) (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term519 _110698 s r _59439 x.
Proof. exact (EQ_MP (@lem4806275 _110698 s r _59439 x) (@lem4806256 _110698 _59439 y y' x s r h1)). Qed.
Lemma lem4806280 {_110698 : Type'} (_59439 : _110698) (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term519 _110698 s r _59439 x.
Proof. exact (@lem4806279 _110698 _59439 y y' x s r h1). Qed.
Lemma lem4806281 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term519 _110698 s r y x.
Proof. exact (@lem4806280 _110698 y y y' x s r h1). Qed.
Lemma lem4806284 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (x : _110698) (y : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) (h3 : @IN _110698 y s) : y = x.
Proof. exact (@lem4806281 _110698 y y' x s r h1 (@lem4806277 _110698 r y' x y s h1 h2 h3)). Qed.
Lemma lem4806285 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (x : _110698) (y : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) (h3 : @IN _110698 y s) : term508 _110698 y x.
Proof. exact (fun h0 : term22 _110698 y x => @lem4806284 _110698 r y' x y s h1 h2 h3). Qed.
Lemma lem4806287 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4806288 {_110698 : Type'} (y : _110698) (x : _110698) : (term508 _110698 y x) = (y = x).
Proof. exact (@lem4806287 (y = x)). Qed.
Lemma lem4806289 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (x : _110698) (y : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) (h3 : @IN _110698 y s) : y = x.
Proof. exact (EQ_MP (@lem4806288 _110698 y x) (@lem4806285 _110698 r y' x y s h1 h2 h3)). Qed.
Lemma lem4806292 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4806294 {_110698 : Type'} (y : _110698) (x : _110698) : (term22 _110698 y x) = (term509 _110698 y x).
Proof. exact (@lem4806292 (y = x)). Qed.
Lemma lem4806297 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) : term509 _110698 y x.
Proof. exact (EQ_MP (@lem4806294 _110698 y x) (@lem4804828 _110698 y s r y' x h1 h2)). Qed.
Lemma lem4806300 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (x : _110698) (y : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) (h3 : @IN _110698 y s) : False.
Proof. exact (@lem4806297 _110698 y s r y' x h1 h2 (@lem4806289 _110698 r y' x y s h1 h2 h3)). Qed.
Lemma lem4806301 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (x : _110698) (y : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) (h3 : @IN _110698 y s) : term454.
Proof. exact (fun h0 : ~ False => @lem4806300 _110698 r y' x y s h1 h2 h3). Qed.
Lemma lem4806303 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4806304 : term454 = False.
Proof. exact (@lem4806303 False). Qed.
Lemma lem4806305 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (x : _110698) (y : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) (h3 : @IN _110698 y s) : False.
Proof. exact (EQ_MP (@lem4806304) (@lem4806301 _110698 r y' x y s h1 h2 h3)). Qed.
Lemma lem4806345 {_110698 : Type'} (x : _110698) (y : _110698) (z : _110698) : term401 _110698 x y z.
Proof. exact (@lem21385 _110698 x y z). Qed.
Lemma lem4806349 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (h1 : @IN _110698 y' s) : @IN _110698 y' s.
Proof. exact (h1). Qed.
Lemma lem4806350 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (h1 : @IN _110698 y' s) : term404 _110698 y' s.
Proof. exact (fun h0 : term331 _110698 y' s => @lem4806349 _110698 y' s h1). Qed.
Lemma lem4806352 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4806353 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) : (term404 _110698 y' s) = (@IN _110698 y' s).
Proof. exact (@lem4806352 (@IN _110698 y' s)). Qed.
Lemma lem4806354 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (h1 : @IN _110698 y' s) : @IN _110698 y' s.
Proof. exact (EQ_MP (@lem4806353 _110698 y' s) (@lem4806350 _110698 y' s h1)). Qed.
Lemma lem4806356 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) : term359 _110698 r x y'.
Proof. exact (EQ_MP (@lem4804910 _110698 r y' y x h2) (@lem4804516 _110698 y y' x s r h1)). Qed.
Lemma lem4806357 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) : term484 _110698 r x y'.
Proof. exact (fun h0 : r x y' => @lem4806356 _110698 y' s r y x h1 h2). Qed.
Lemma lem4806359 (p : Prop) : (term406 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4806360 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (y' : _110698) : (term484 _110698 r x y') = (term359 _110698 r x y').
Proof. exact (@lem4806359 (r x y')). Qed.
Lemma lem4806361 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) : term359 _110698 r x y'.
Proof. exact (EQ_MP (@lem4806360 _110698 r x y') (@lem4806357 _110698 y' s r y x h1 h2)). Qed.
Lemma lem4806367 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4806368 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) (_59442 : _110698) : (term384 _110698 s r x _59442) = (term520 _110698 s r x _59442).
Proof. exact (@lem4806367 (_59442 = x) (term331 _110698 _59442 s) (r x _59442)). Qed.
Lemma lem4806384 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4806385 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59442 : _110698) (s : _110698 -> Prop) : (term423 _110698 s r x _59442) = (term424 _110698 r x _59442 s).
Proof. exact (@lem4806384 (r x _59442) (term331 _110698 _59442 s)). Qed.
Lemma lem4806391 {_110698 : Type'} (_59442 : _110698) (x : _110698) : (term425 _110698 _59442 x) = (term425 _110698 _59442 x).
Proof. exact (eq_refl (term425 _110698 _59442 x)). Qed.
Lemma lem4806392 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59442 : _110698) (s : _110698 -> Prop) : (term520 _110698 s r x _59442) = (term521 _110698 r x _59442 s).
Proof. exact (MK_COMB (@lem4806391 _110698 _59442 x) (@lem4806385 _110698 r x _59442 s)). Qed.
Lemma lem4806396 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4806397 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59442 : _110698) (s : _110698 -> Prop) : (term521 _110698 r x _59442 s) = (term522 _110698 r x _59442 s).
Proof. exact (@lem4806396 (r x _59442) (_59442 = x) (term331 _110698 _59442 s)). Qed.
Lemma lem4806415 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59442 : _110698) (s : _110698 -> Prop) : (term520 _110698 s r x _59442) = (term522 _110698 r x _59442 s).
Proof. exact (TRANS (@lem4806392 _110698 r x _59442 s) (@lem4806397 _110698 r x _59442 s)). Qed.
Lemma lem4806416 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59442 : _110698) (s : _110698 -> Prop) : (term384 _110698 s r x _59442) = (term522 _110698 r x _59442 s).
Proof. exact (TRANS (@lem4806368 _110698 s r x _59442) (@lem4806415 _110698 r x _59442 s)). Qed.
Lemma lem4806417 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4806418 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59442 : _110698) (s : _110698 -> Prop) : (term523 _110698 s r x _59442) = (term524 _110698 r x _59442 s).
Proof. exact (MK_COMB (@lem4806417) (@lem4806416 _110698 r x _59442 s)). Qed.
Lemma lem4806434 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4806435 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59442 : _110698) (s : _110698 -> Prop) : (term423 _110698 s r x _59442) = (term424 _110698 r x _59442 s).
Proof. exact (@lem4806434 (r x _59442) (term331 _110698 _59442 s)). Qed.
Lemma lem4806441 {_110698 : Type'} (_59442 : _110698) (x : _110698) : (term425 _110698 _59442 x) = (term425 _110698 _59442 x).
Proof. exact (eq_refl (term425 _110698 _59442 x)). Qed.
Lemma lem4806442 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59442 : _110698) (s : _110698 -> Prop) : (term520 _110698 s r x _59442) = (term521 _110698 r x _59442 s).
Proof. exact (MK_COMB (@lem4806441 _110698 _59442 x) (@lem4806435 _110698 r x _59442 s)). Qed.
Lemma lem4806446 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4806447 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59442 : _110698) (s : _110698 -> Prop) : (term521 _110698 r x _59442 s) = (term522 _110698 r x _59442 s).
Proof. exact (@lem4806446 (r x _59442) (_59442 = x) (term331 _110698 _59442 s)). Qed.
Lemma lem4806465 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59442 : _110698) (s : _110698 -> Prop) : (term520 _110698 s r x _59442) = (term522 _110698 r x _59442 s).
Proof. exact (TRANS (@lem4806442 _110698 r x _59442 s) (@lem4806447 _110698 r x _59442 s)). Qed.
Lemma lem4806466 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59442 : _110698) (s : _110698 -> Prop) : ((term384 _110698 s r x _59442) = (term520 _110698 s r x _59442)) = ((term522 _110698 r x _59442 s) = (term522 _110698 r x _59442 s)).
Proof. exact (MK_COMB (@lem4806418 _110698 r x _59442 s) (@lem4806465 _110698 r x _59442 s)). Qed.
Lemma lem4806468 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4806469 (x : Prop) : (x = x) = True.
Proof. exact (@lem4806468 Prop x). Qed.
Lemma lem4806470 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59442 : _110698) (s : _110698 -> Prop) : ((term522 _110698 r x _59442 s) = (term522 _110698 r x _59442 s)) = True.
Proof. exact (@lem4806469 (term522 _110698 r x _59442 s)). Qed.
Lemma lem4806471 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) (_59442 : _110698) : ((term384 _110698 s r x _59442) = (term520 _110698 s r x _59442)) = True.
Proof. exact (TRANS (@lem4806466 _110698 r x _59442 s) (@lem4806470 _110698 r x _59442 s)). Qed.
Lemma lem4806472 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) (_59442 : _110698) : True = ((term384 _110698 s r x _59442) = (term520 _110698 s r x _59442)).
Proof. exact (SYM (@lem4806471 _110698 s r x _59442)). Qed.
Lemma lem4806473 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) (_59442 : _110698) : (term384 _110698 s r x _59442) = (term520 _110698 s r x _59442).
Proof. exact (EQ_MP (@lem4806472 _110698 s r x _59442) (@lem0)). Qed.
Lemma lem4806474 {_110698 : Type'} (_59442 : _110698) (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term520 _110698 s r x _59442.
Proof. exact (EQ_MP (@lem4806473 _110698 s r x _59442) (@lem4804952 _110698 _59442 y y' x s r h1)). Qed.
Lemma lem4806476 (b : Prop) (a : Prop) : (a \/ b) = (term407 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4806477 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59442 : _110698) (x : _110698) : (term520 _110698 s r x _59442) = (term525 _110698 s r _59442 x).
Proof. exact (@lem4806476 (term423 _110698 s r x _59442) (_59442 = x)). Qed.
Lemma lem4806479 (a : Prop) (b : Prop) : (term410 a b) = (term411 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4806480 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) (_59442 : _110698) : (term501 _110698 s r x _59442) = (term502 _110698 s r x _59442).
Proof. exact (@lem4806479 (term331 _110698 _59442 s) (r x _59442)). Qed.
Lemma lem4806482 (a : Prop) : (term62 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4806483 {_110698 : Type'} (_59442 : _110698) (s : _110698 -> Prop) : (term443 _110698 _59442 s) = (@IN _110698 _59442 s).
Proof. exact (@lem4806482 (@IN _110698 _59442 s)). Qed.
Lemma lem4806484 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4806485 {_110698 : Type'} (_59442 : _110698) (s : _110698 -> Prop) : (term444 _110698 _59442 s) = (term445 _110698 _59442 s).
Proof. exact (MK_COMB (@lem4806484) (@lem4806483 _110698 _59442 s)). Qed.
Lemma lem4806486 {_110698 : Type'} (r : type1402 _110698) (x : _110698) (_59442 : _110698) : (term359 _110698 r x _59442) = (term359 _110698 r x _59442).
Proof. exact (eq_refl (term359 _110698 r x _59442)). Qed.
Lemma lem4806487 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) (_59442 : _110698) : (term502 _110698 s r x _59442) = (term503 _110698 s r x _59442).
Proof. exact (MK_COMB (@lem4806485 _110698 _59442 s) (@lem4806486 _110698 r x _59442)). Qed.
Lemma lem4806488 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) (_59442 : _110698) : (term501 _110698 s r x _59442) = (term503 _110698 s r x _59442).
Proof. exact (TRANS (@lem4806480 _110698 s r x _59442) (@lem4806487 _110698 s r x _59442)). Qed.
Lemma lem4806489 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4806490 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (x : _110698) (_59442 : _110698) : (term526 _110698 s r x _59442) = (term527 _110698 s r x _59442).
Proof. exact (MK_COMB (@lem4806489) (@lem4806488 _110698 s r x _59442)). Qed.
Lemma lem4806491 {_110698 : Type'} (_59442 : _110698) (x : _110698) : (_59442 = x) = (_59442 = x).
Proof. exact (eq_refl (_59442 = x)). Qed.
Lemma lem4806492 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59442 : _110698) (x : _110698) : (term525 _110698 s r _59442 x) = (term528 _110698 s r _59442 x).
Proof. exact (MK_COMB (@lem4806490 _110698 s r x _59442) (@lem4806491 _110698 _59442 x)). Qed.
Lemma lem4806493 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59442 : _110698) (x : _110698) : (term520 _110698 s r x _59442) = (term528 _110698 s r _59442 x).
Proof. exact (TRANS (@lem4806477 _110698 s r _59442 x) (@lem4806492 _110698 s r _59442 x)). Qed.
Lemma lem4806495 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : term503 _110698 s r x y'.
Proof. exact (conj (@lem4806354 _110698 y' s h3) (@lem4806361 _110698 y' s r y x h1 h2)). Qed.
Lemma lem4806497 {_110698 : Type'} (_59442 : _110698) (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term528 _110698 s r _59442 x.
Proof. exact (EQ_MP (@lem4806493 _110698 s r _59442 x) (@lem4806474 _110698 _59442 y y' x s r h1)). Qed.
Lemma lem4806498 {_110698 : Type'} (_59442 : _110698) (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term528 _110698 s r _59442 x.
Proof. exact (@lem4806497 _110698 _59442 y y' x s r h1). Qed.
Lemma lem4806499 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term528 _110698 s r y' x.
Proof. exact (@lem4806498 _110698 y' y y' x s r h1). Qed.
Lemma lem4806502 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : y' = x.
Proof. exact (@lem4806499 _110698 y y' x s r h1 (@lem4806495 _110698 r y x y' s h1 h2 h3)). Qed.
Lemma lem4806503 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : term508 _110698 y' x.
Proof. exact (fun h0 : term22 _110698 y' x => @lem4806502 _110698 r y x y' s h1 h2 h3). Qed.
Lemma lem4806505 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4806506 {_110698 : Type'} (y' : _110698) (x : _110698) : (term508 _110698 y' x) = (y' = x).
Proof. exact (@lem4806505 (y' = x)). Qed.
Lemma lem4806507 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : y' = x.
Proof. exact (EQ_MP (@lem4806506 _110698 y' x) (@lem4806503 _110698 r y x y' s h1 h2 h3)). Qed.
Lemma lem4806509 {_110698 : Type'} (x : _110698) : x = x.
Proof. exact (@lem21386 _110698 x). Qed.
Lemma lem4806510 {_110698 : Type'} (x : _110698) : x = x.
Proof. exact (@lem4806509 _110698 x). Qed.
Lemma lem4806511 {_110698 : Type'} (y' : _110698) : y' = y'.
Proof. exact (@lem4806510 _110698 y'). Qed.
Lemma lem4806512 {_110698 : Type'} (y' : _110698) : term402 _110698 y'.
Proof. exact (fun h0 : term392 _110698 y' => @lem4806511 _110698 y'). Qed.
Lemma lem4806514 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4806515 {_110698 : Type'} (y' : _110698) : (term402 _110698 y') = (y' = y').
Proof. exact (@lem4806514 (y' = y')). Qed.
Lemma lem4806516 {_110698 : Type'} (y' : _110698) : y' = y'.
Proof. exact (EQ_MP (@lem4806515 _110698 y') (@lem4806512 _110698 y')). Qed.
Lemma lem4806534 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4806535 {_110698 : Type'} (y : _110698) (x : _110698) (z : _110698) : (term409 _110698 x y z) = (term529 _110698 y x z).
Proof. exact (@lem4806534 (y = z) (term22 _110698 x z)). Qed.
Lemma lem4806545 {_110698 : Type'} (x : _110698) (y : _110698) : (term375 _110698 x y) = (term375 _110698 x y).
Proof. exact (eq_refl (term375 _110698 x y)). Qed.
Lemma lem4806546 {_110698 : Type'} (y : _110698) (x : _110698) (z : _110698) : (term401 _110698 x y z) = (term530 _110698 y x z).
Proof. exact (MK_COMB (@lem4806545 _110698 x y) (@lem4806535 _110698 y x z)). Qed.
Lemma lem4806550 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4806551 {_110698 : Type'} (y : _110698) (x : _110698) (z : _110698) : (term530 _110698 y x z) = (term531 _110698 y x z).
Proof. exact (@lem4806550 (y = z) (term22 _110698 x y) (term22 _110698 x z)). Qed.
Lemma lem4806573 {_110698 : Type'} (y : _110698) (x : _110698) (z : _110698) : (term401 _110698 x y z) = (term531 _110698 y x z).
Proof. exact (TRANS (@lem4806546 _110698 y x z) (@lem4806551 _110698 y x z)). Qed.
Lemma lem4806574 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4806575 {_110698 : Type'} (y : _110698) (x : _110698) (z : _110698) : (term532 _110698 x y z) = (term533 _110698 y x z).
Proof. exact (MK_COMB (@lem4806574) (@lem4806573 _110698 y x z)). Qed.
Lemma lem4806597 {_110698 : Type'} (y : _110698) (x : _110698) (z : _110698) : (term531 _110698 y x z) = (term531 _110698 y x z).
Proof. exact (eq_refl (term531 _110698 y x z)). Qed.
Lemma lem4806598 {_110698 : Type'} (y : _110698) (x : _110698) (z : _110698) : ((term401 _110698 x y z) = (term531 _110698 y x z)) = ((term531 _110698 y x z) = (term531 _110698 y x z)).
Proof. exact (MK_COMB (@lem4806575 _110698 y x z) (@lem4806597 _110698 y x z)). Qed.
Lemma lem4806600 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4806601 (x : Prop) : (x = x) = True.
Proof. exact (@lem4806600 Prop x). Qed.
Lemma lem4806602 {_110698 : Type'} (y : _110698) (x : _110698) (z : _110698) : ((term531 _110698 y x z) = (term531 _110698 y x z)) = True.
Proof. exact (@lem4806601 (term531 _110698 y x z)). Qed.
Lemma lem4806603 {_110698 : Type'} (y : _110698) (x : _110698) (z : _110698) : ((term401 _110698 x y z) = (term531 _110698 y x z)) = True.
Proof. exact (TRANS (@lem4806598 _110698 y x z) (@lem4806602 _110698 y x z)). Qed.
Lemma lem4806604 {_110698 : Type'} (y : _110698) (x : _110698) (z : _110698) : True = ((term401 _110698 x y z) = (term531 _110698 y x z)).
Proof. exact (SYM (@lem4806603 _110698 y x z)). Qed.
Lemma lem4806605 {_110698 : Type'} (y : _110698) (x : _110698) (z : _110698) : (term401 _110698 x y z) = (term531 _110698 y x z).
Proof. exact (EQ_MP (@lem4806604 _110698 y x z) (@lem0)). Qed.
Lemma lem4806606 {_110698 : Type'} (y : _110698) (x : _110698) (z : _110698) : term531 _110698 y x z.
Proof. exact (EQ_MP (@lem4806605 _110698 y x z) (@lem4806345 _110698 x y z)). Qed.
Lemma lem4806608 (b : Prop) (a : Prop) : (a \/ b) = (term407 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4806609 {_110698 : Type'} (x : _110698) (y : _110698) (z : _110698) : (term531 _110698 y x z) = (term534 _110698 x y z).
Proof. exact (@lem4806608 (term535 _110698 y x z) (y = z)). Qed.
Lemma lem4806611 (a : Prop) (b : Prop) : (term410 a b) = (term411 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4806612 {_110698 : Type'} (y : _110698) (x : _110698) (z : _110698) : (term536 _110698 y x z) = (term537 _110698 y x z).
Proof. exact (@lem4806611 (term22 _110698 x y) (term22 _110698 x z)). Qed.
Lemma lem4806614 (a : Prop) : (term62 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4806615 {_110698 : Type'} (x : _110698) (y : _110698) : (term74 _110698 x y) = (x = y).
Proof. exact (@lem4806614 (x = y)). Qed.
Lemma lem4806616 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4806617 {_110698 : Type'} (x : _110698) (y : _110698) : (term414 _110698 x y) = (term415 _110698 x y).
Proof. exact (MK_COMB (@lem4806616) (@lem4806615 _110698 x y)). Qed.
Lemma lem4806619 (a : Prop) : (term62 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4806620 {_110698 : Type'} (x : _110698) (z : _110698) : (term74 _110698 x z) = (x = z).
Proof. exact (@lem4806619 (x = z)). Qed.
Lemma lem4806621 {_110698 : Type'} (y : _110698) (x : _110698) (z : _110698) : (term537 _110698 y x z) = (term538 _110698 y x z).
Proof. exact (MK_COMB (@lem4806617 _110698 x y) (@lem4806620 _110698 x z)). Qed.
Lemma lem4806622 {_110698 : Type'} (y : _110698) (x : _110698) (z : _110698) : (term536 _110698 y x z) = (term538 _110698 y x z).
Proof. exact (TRANS (@lem4806612 _110698 y x z) (@lem4806621 _110698 y x z)). Qed.
Lemma lem4806623 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4806624 {_110698 : Type'} (y : _110698) (x : _110698) (z : _110698) : (term539 _110698 y x z) = (term540 _110698 y x z).
Proof. exact (MK_COMB (@lem4806623) (@lem4806622 _110698 y x z)). Qed.
Lemma lem4806625 {_110698 : Type'} (y : _110698) (z : _110698) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem4806626 {_110698 : Type'} (x : _110698) (y : _110698) (z : _110698) : (term534 _110698 x y z) = (term541 _110698 x y z).
Proof. exact (MK_COMB (@lem4806624 _110698 y x z) (@lem4806625 _110698 y z)). Qed.
Lemma lem4806627 {_110698 : Type'} (x : _110698) (y : _110698) (z : _110698) : (term531 _110698 y x z) = (term541 _110698 x y z).
Proof. exact (TRANS (@lem4806609 _110698 x y z) (@lem4806626 _110698 x y z)). Qed.
Lemma lem4806629 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : term542 _110698 x y'.
Proof. exact (conj (@lem4806507 _110698 r y x y' s h1 h2 h3) (@lem4806516 _110698 y')). Qed.
Lemma lem4806631 {_110698 : Type'} (x : _110698) (y : _110698) (z : _110698) : term541 _110698 x y z.
Proof. exact (EQ_MP (@lem4806627 _110698 x y z) (@lem4806606 _110698 y x z)). Qed.
Lemma lem4806632 {_110698 : Type'} (x : _110698) (y : _110698) (z : _110698) : term541 _110698 x y z.
Proof. exact (@lem4806631 _110698 x y z). Qed.
Lemma lem4806633 {_110698 : Type'} (x : _110698) (y' : _110698) : term543 _110698 x y'.
Proof. exact (@lem4806632 _110698 y' x y'). Qed.
Lemma lem4806636 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : x = y'.
Proof. exact (@lem4806633 _110698 x y' (@lem4806629 _110698 r y x y' s h1 h2 h3)). Qed.
Lemma lem4806637 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : term508 _110698 x y'.
Proof. exact (fun h0 : term22 _110698 x y' => @lem4806636 _110698 r y x y' s h1 h2 h3). Qed.
Lemma lem4806639 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4806640 {_110698 : Type'} (x : _110698) (y' : _110698) : (term508 _110698 x y') = (x = y').
Proof. exact (@lem4806639 (x = y')). Qed.
Lemma lem4806641 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : x = y'.
Proof. exact (EQ_MP (@lem4806640 _110698 x y') (@lem4806637 _110698 r y x y' s h1 h2 h3)). Qed.
Lemma lem4806644 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4806646 {_110698 : Type'} (x : _110698) (y' : _110698) : (term22 _110698 x y') = (term509 _110698 x y').
Proof. exact (@lem4806644 (x = y')). Qed.
Lemma lem4806649 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) : term509 _110698 x y'.
Proof. exact (EQ_MP (@lem4806646 _110698 x y') (@lem4804924 _110698 y' s r y x h1 h2)). Qed.
Lemma lem4806652 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : False.
Proof. exact (@lem4806649 _110698 y' s r y x h1 h2 (@lem4806641 _110698 r y x y' s h1 h2 h3)). Qed.
Lemma lem4806653 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : term454.
Proof. exact (fun h0 : ~ False => @lem4806652 _110698 r y x y' s h1 h2 h3). Qed.
Lemma lem4806655 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4806656 : term454 = False.
Proof. exact (@lem4806655 False). Qed.
Lemma lem4806657 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : False.
Proof. exact (EQ_MP (@lem4806656) (@lem4806653 _110698 r y x y' s h1 h2 h3)). Qed.
Lemma lem4806701 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) (h1 : @IN _110698 y s) : @IN _110698 y s.
Proof. exact (h1). Qed.
Lemma lem4806702 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) (h1 : @IN _110698 y s) : term404 _110698 y s.
Proof. exact (fun h0 : term331 _110698 y s => @lem4806701 _110698 y s h1). Qed.
Lemma lem4806704 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4806705 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) : (term404 _110698 y s) = (@IN _110698 y s).
Proof. exact (@lem4806704 (@IN _110698 y s)). Qed.
Lemma lem4806706 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) (h1 : @IN _110698 y s) : @IN _110698 y s.
Proof. exact (EQ_MP (@lem4806705 _110698 y s) (@lem4806702 _110698 y s h1)). Qed.
Lemma lem4806708 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (h1 : @IN _110698 y' s) : @IN _110698 y' s.
Proof. exact (h1). Qed.
Lemma lem4806709 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (h1 : @IN _110698 y' s) : term404 _110698 y' s.
Proof. exact (fun h0 : term331 _110698 y' s => @lem4806708 _110698 y' s h1). Qed.
Lemma lem4806711 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4806712 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) : (term404 _110698 y' s) = (@IN _110698 y' s).
Proof. exact (@lem4806711 (@IN _110698 y' s)). Qed.
Lemma lem4806713 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (h1 : @IN _110698 y' s) : @IN _110698 y' s.
Proof. exact (EQ_MP (@lem4806712 _110698 y' s) (@lem4806709 _110698 y' s h1)). Qed.
Lemma lem4806715 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term359 _110698 r y y'.
Proof. exact (proj2 (@lem4803500 _110698 y y' x s r h1)). Qed.
Lemma lem4806716 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term484 _110698 r y y'.
Proof. exact (fun h0 : r y y' => @lem4806715 _110698 y y' x s r h1). Qed.
Lemma lem4806718 (p : Prop) : (term406 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4806719 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (y' : _110698) : (term484 _110698 r y y') = (term359 _110698 r y y').
Proof. exact (@lem4806718 (r y y')). Qed.
Lemma lem4806720 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term359 _110698 r y y'.
Proof. exact (EQ_MP (@lem4806719 _110698 r y y') (@lem4806716 _110698 y y' x s r h1)). Qed.
Lemma lem4806736 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4806737 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) : (term374 _110698 s r _59446 _59447) = (term422 _110698 s r _59446 _59447).
Proof. exact (@lem4806736 (_59446 = _59447) (term331 _110698 _59447 s) (r _59446 _59447)). Qed.
Lemma lem4806753 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4806754 {_110698 : Type'} (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) (s : _110698 -> Prop) : (term423 _110698 s r _59446 _59447) = (term424 _110698 r _59446 _59447 s).
Proof. exact (@lem4806753 (r _59446 _59447) (term331 _110698 _59447 s)). Qed.
Lemma lem4806760 {_110698 : Type'} (_59446 : _110698) (_59447 : _110698) : (term425 _110698 _59446 _59447) = (term425 _110698 _59446 _59447).
Proof. exact (eq_refl (term425 _110698 _59446 _59447)). Qed.
Lemma lem4806761 {_110698 : Type'} (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) (s : _110698 -> Prop) : (term422 _110698 s r _59446 _59447) = (term426 _110698 r _59446 _59447 s).
Proof. exact (MK_COMB (@lem4806760 _110698 _59446 _59447) (@lem4806754 _110698 r _59446 _59447 s)). Qed.
Lemma lem4806765 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4806766 {_110698 : Type'} (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) (s : _110698 -> Prop) : (term426 _110698 r _59446 _59447 s) = (term427 _110698 r _59446 _59447 s).
Proof. exact (@lem4806765 (r _59446 _59447) (_59446 = _59447) (term331 _110698 _59447 s)). Qed.
Lemma lem4806784 {_110698 : Type'} (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) (s : _110698 -> Prop) : (term422 _110698 s r _59446 _59447) = (term427 _110698 r _59446 _59447 s).
Proof. exact (TRANS (@lem4806761 _110698 r _59446 _59447 s) (@lem4806766 _110698 r _59446 _59447 s)). Qed.
Lemma lem4806785 {_110698 : Type'} (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) (s : _110698 -> Prop) : (term374 _110698 s r _59446 _59447) = (term427 _110698 r _59446 _59447 s).
Proof. exact (TRANS (@lem4806737 _110698 s r _59446 _59447) (@lem4806784 _110698 r _59446 _59447 s)). Qed.
Lemma lem4806786 {_110698 : Type'} (_59446 : _110698) (s : _110698 -> Prop) : (term109 _110698 _59446 s) = (term109 _110698 _59446 s).
Proof. exact (eq_refl (term109 _110698 _59446 s)). Qed.
Lemma lem4806787 {_110698 : Type'} (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) (s : _110698 -> Prop) : (term382 _110698 s r _59446 _59447) = (term485 _110698 r _59446 _59447 s).
Proof. exact (MK_COMB (@lem4806786 _110698 _59446 s) (@lem4806785 _110698 r _59446 _59447 s)). Qed.
Lemma lem4806791 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4806792 {_110698 : Type'} (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) (s : _110698 -> Prop) : (term485 _110698 r _59446 _59447 s) = (term486 _110698 r _59446 _59447 s).
Proof. exact (@lem4806791 (r _59446 _59447) (term331 _110698 _59446 s) (term430 _110698 _59446 _59447 s)). Qed.
Lemma lem4806806 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4806807 {_110698 : Type'} (_59446 : _110698) (_59447 : _110698) (s : _110698 -> Prop) : (term487 _110698 _59446 _59447 s) = (term488 _110698 _59446 _59447 s).
Proof. exact (@lem4806806 (_59446 = _59447) (term331 _110698 _59446 s) (term331 _110698 _59447 s)). Qed.
Lemma lem4806825 {_110698 : Type'} (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) : (term433 _110698 r _59446 _59447) = (term433 _110698 r _59446 _59447).
Proof. exact (eq_refl (term433 _110698 r _59446 _59447)). Qed.
Lemma lem4806826 {_110698 : Type'} (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) (s : _110698 -> Prop) : (term486 _110698 r _59446 _59447 s) = (term489 _110698 r _59446 _59447 s).
Proof. exact (MK_COMB (@lem4806825 _110698 r _59446 _59447) (@lem4806807 _110698 _59446 _59447 s)). Qed.
Lemma lem4806837 {_110698 : Type'} (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) (s : _110698 -> Prop) : (term485 _110698 r _59446 _59447 s) = (term489 _110698 r _59446 _59447 s).
Proof. exact (TRANS (@lem4806792 _110698 r _59446 _59447 s) (@lem4806826 _110698 r _59446 _59447 s)). Qed.
Lemma lem4806838 {_110698 : Type'} (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) (s : _110698 -> Prop) : (term382 _110698 s r _59446 _59447) = (term489 _110698 r _59446 _59447 s).
Proof. exact (TRANS (@lem4806787 _110698 r _59446 _59447 s) (@lem4806837 _110698 r _59446 _59447 s)). Qed.
Lemma lem4806839 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4806840 {_110698 : Type'} (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) (s : _110698 -> Prop) : (term490 _110698 s r _59446 _59447) = (term491 _110698 r _59446 _59447 s).
Proof. exact (MK_COMB (@lem4806839) (@lem4806838 _110698 r _59446 _59447 s)). Qed.
Lemma lem4806866 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4806867 {_110698 : Type'} (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) (s : _110698 -> Prop) : (term423 _110698 s r _59446 _59447) = (term424 _110698 r _59446 _59447 s).
Proof. exact (@lem4806866 (r _59446 _59447) (term331 _110698 _59447 s)). Qed.
Lemma lem4806873 {_110698 : Type'} (_59446 : _110698) (s : _110698 -> Prop) : (term109 _110698 _59446 s) = (term109 _110698 _59446 s).
Proof. exact (eq_refl (term109 _110698 _59446 s)). Qed.
Lemma lem4806874 {_110698 : Type'} (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) (s : _110698 -> Prop) : (term492 _110698 s r _59446 _59447) = (term493 _110698 r _59446 _59447 s).
Proof. exact (MK_COMB (@lem4806873 _110698 _59446 s) (@lem4806867 _110698 r _59446 _59447 s)). Qed.
Lemma lem4806878 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4806879 {_110698 : Type'} (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) (s : _110698 -> Prop) : (term493 _110698 r _59446 _59447 s) = (term494 _110698 r _59446 _59447 s).
Proof. exact (@lem4806878 (r _59446 _59447) (term331 _110698 _59446 s) (term331 _110698 _59447 s)). Qed.
Lemma lem4806895 {_110698 : Type'} (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) (s : _110698 -> Prop) : (term492 _110698 s r _59446 _59447) = (term494 _110698 r _59446 _59447 s).
Proof. exact (TRANS (@lem4806874 _110698 r _59446 _59447 s) (@lem4806879 _110698 r _59446 _59447 s)). Qed.
Lemma lem4806896 {_110698 : Type'} (_59446 : _110698) (_59447 : _110698) : (term425 _110698 _59446 _59447) = (term425 _110698 _59446 _59447).
Proof. exact (eq_refl (term425 _110698 _59446 _59447)). Qed.
Lemma lem4806897 {_110698 : Type'} (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) (s : _110698 -> Prop) : (term495 _110698 s r _59446 _59447) = (term496 _110698 r _59446 _59447 s).
Proof. exact (MK_COMB (@lem4806896 _110698 _59446 _59447) (@lem4806895 _110698 r _59446 _59447 s)). Qed.
Lemma lem4806901 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4806902 {_110698 : Type'} (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) (s : _110698 -> Prop) : (term496 _110698 r _59446 _59447 s) = (term489 _110698 r _59446 _59447 s).
Proof. exact (@lem4806901 (r _59446 _59447) (_59446 = _59447) (term497 _110698 _59446 _59447 s)). Qed.
Lemma lem4806930 {_110698 : Type'} (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) (s : _110698 -> Prop) : (term495 _110698 s r _59446 _59447) = (term489 _110698 r _59446 _59447 s).
Proof. exact (TRANS (@lem4806897 _110698 r _59446 _59447 s) (@lem4806902 _110698 r _59446 _59447 s)). Qed.
Lemma lem4806931 {_110698 : Type'} (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) (s : _110698 -> Prop) : ((term382 _110698 s r _59446 _59447) = (term495 _110698 s r _59446 _59447)) = ((term489 _110698 r _59446 _59447 s) = (term489 _110698 r _59446 _59447 s)).
Proof. exact (MK_COMB (@lem4806840 _110698 r _59446 _59447 s) (@lem4806930 _110698 r _59446 _59447 s)). Qed.
Lemma lem4806933 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4806934 (x : Prop) : (x = x) = True.
Proof. exact (@lem4806933 Prop x). Qed.
Lemma lem4806935 {_110698 : Type'} (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) (s : _110698 -> Prop) : ((term489 _110698 r _59446 _59447 s) = (term489 _110698 r _59446 _59447 s)) = True.
Proof. exact (@lem4806934 (term489 _110698 r _59446 _59447 s)). Qed.
Lemma lem4806936 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) : ((term382 _110698 s r _59446 _59447) = (term495 _110698 s r _59446 _59447)) = True.
Proof. exact (TRANS (@lem4806931 _110698 r _59446 _59447 s) (@lem4806935 _110698 r _59446 _59447 s)). Qed.
Lemma lem4806937 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) : True = ((term382 _110698 s r _59446 _59447) = (term495 _110698 s r _59446 _59447)).
Proof. exact (SYM (@lem4806936 _110698 s r _59446 _59447)). Qed.
Lemma lem4806938 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) : (term382 _110698 s r _59446 _59447) = (term495 _110698 s r _59446 _59447).
Proof. exact (EQ_MP (@lem4806937 _110698 s r _59446 _59447) (@lem0)). Qed.
Lemma lem4806939 {_110698 : Type'} (_59446 : _110698) (_59447 : _110698) (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term495 _110698 s r _59446 _59447.
Proof. exact (EQ_MP (@lem4806938 _110698 s r _59446 _59447) (@lem4804564 _110698 _59446 _59447 y y' x s r h1)). Qed.
Lemma lem4806941 (b : Prop) (a : Prop) : (a \/ b) = (term407 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4806942 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) : (term495 _110698 s r _59446 _59447) = (term498 _110698 s r _59446 _59447).
Proof. exact (@lem4806941 (term492 _110698 s r _59446 _59447) (_59446 = _59447)). Qed.
Lemma lem4806944 (a : Prop) (b : Prop) : (term410 a b) = (term411 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4806945 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) : (term499 _110698 s r _59446 _59447) = (term500 _110698 s r _59446 _59447).
Proof. exact (@lem4806944 (term331 _110698 _59446 s) (term423 _110698 s r _59446 _59447)). Qed.
Lemma lem4806947 (a : Prop) : (term62 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4806948 {_110698 : Type'} (_59446 : _110698) (s : _110698 -> Prop) : (term443 _110698 _59446 s) = (@IN _110698 _59446 s).
Proof. exact (@lem4806947 (@IN _110698 _59446 s)). Qed.
Lemma lem4806949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4806950 {_110698 : Type'} (_59446 : _110698) (s : _110698 -> Prop) : (term444 _110698 _59446 s) = (term445 _110698 _59446 s).
Proof. exact (MK_COMB (@lem4806949) (@lem4806948 _110698 _59446 s)). Qed.
Lemma lem4806952 (a : Prop) (b : Prop) : (term410 a b) = (term411 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4806953 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) : (term501 _110698 s r _59446 _59447) = (term502 _110698 s r _59446 _59447).
Proof. exact (@lem4806952 (term331 _110698 _59447 s) (r _59446 _59447)). Qed.
Lemma lem4806955 (a : Prop) : (term62 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4806956 {_110698 : Type'} (_59447 : _110698) (s : _110698 -> Prop) : (term443 _110698 _59447 s) = (@IN _110698 _59447 s).
Proof. exact (@lem4806955 (@IN _110698 _59447 s)). Qed.
Lemma lem4806957 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4806958 {_110698 : Type'} (_59447 : _110698) (s : _110698 -> Prop) : (term444 _110698 _59447 s) = (term445 _110698 _59447 s).
Proof. exact (MK_COMB (@lem4806957) (@lem4806956 _110698 _59447 s)). Qed.
Lemma lem4806959 {_110698 : Type'} (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) : (term359 _110698 r _59446 _59447) = (term359 _110698 r _59446 _59447).
Proof. exact (eq_refl (term359 _110698 r _59446 _59447)). Qed.
Lemma lem4806960 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) : (term502 _110698 s r _59446 _59447) = (term503 _110698 s r _59446 _59447).
Proof. exact (MK_COMB (@lem4806958 _110698 _59447 s) (@lem4806959 _110698 r _59446 _59447)). Qed.
Lemma lem4806961 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) : (term501 _110698 s r _59446 _59447) = (term503 _110698 s r _59446 _59447).
Proof. exact (TRANS (@lem4806953 _110698 s r _59446 _59447) (@lem4806960 _110698 s r _59446 _59447)). Qed.
Lemma lem4806962 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) : (term500 _110698 s r _59446 _59447) = (term504 _110698 s r _59446 _59447).
Proof. exact (MK_COMB (@lem4806950 _110698 _59446 s) (@lem4806961 _110698 s r _59446 _59447)). Qed.
Lemma lem4806963 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) : (term499 _110698 s r _59446 _59447) = (term504 _110698 s r _59446 _59447).
Proof. exact (TRANS (@lem4806945 _110698 s r _59446 _59447) (@lem4806962 _110698 s r _59446 _59447)). Qed.
Lemma lem4806964 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4806965 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) : (term505 _110698 s r _59446 _59447) = (term506 _110698 s r _59446 _59447).
Proof. exact (MK_COMB (@lem4806964) (@lem4806963 _110698 s r _59446 _59447)). Qed.
Lemma lem4806966 {_110698 : Type'} (_59446 : _110698) (_59447 : _110698) : (_59446 = _59447) = (_59446 = _59447).
Proof. exact (eq_refl (_59446 = _59447)). Qed.
Lemma lem4806967 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) : (term498 _110698 s r _59446 _59447) = (term507 _110698 s r _59446 _59447).
Proof. exact (MK_COMB (@lem4806965 _110698 s r _59446 _59447) (@lem4806966 _110698 _59446 _59447)). Qed.
Lemma lem4806968 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (_59446 : _110698) (_59447 : _110698) : (term495 _110698 s r _59446 _59447) = (term507 _110698 s r _59446 _59447).
Proof. exact (TRANS (@lem4806942 _110698 s r _59446 _59447) (@lem4806967 _110698 s r _59446 _59447)). Qed.
Lemma lem4806970 {_110698 : Type'} (y : _110698) (x : _110698) (r : type1402 _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : @IN _110698 y' s) : term503 _110698 s r y y'.
Proof. exact (conj (@lem4806713 _110698 y' s h2) (@lem4806720 _110698 y y' x s r h1)). Qed.
Lemma lem4806971 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (y : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : @IN _110698 y s) (h3 : @IN _110698 y' s) : term504 _110698 s r y y'.
Proof. exact (conj (@lem4806706 _110698 y s h2) (@lem4806970 _110698 y x r y' s h1 h3)). Qed.
Lemma lem4806973 {_110698 : Type'} (_59446 : _110698) (_59447 : _110698) (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term507 _110698 s r _59446 _59447.
Proof. exact (EQ_MP (@lem4806968 _110698 s r _59446 _59447) (@lem4806939 _110698 _59446 _59447 y y' x s r h1)). Qed.
Lemma lem4806974 {_110698 : Type'} (_59446 : _110698) (_59447 : _110698) (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term507 _110698 s r _59446 _59447.
Proof. exact (@lem4806973 _110698 _59446 _59447 y y' x s r h1). Qed.
Lemma lem4806975 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term507 _110698 s r y y'.
Proof. exact (@lem4806974 _110698 y y' y y' x s r h1). Qed.
Lemma lem4806978 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (y : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : @IN _110698 y s) (h3 : @IN _110698 y' s) : y = y'.
Proof. exact (@lem4806975 _110698 y y' x s r h1 (@lem4806971 _110698 x r y y' s h1 h2 h3)). Qed.
Lemma lem4806979 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (y : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : @IN _110698 y s) (h3 : @IN _110698 y' s) : term508 _110698 y y'.
Proof. exact (fun h0 : term22 _110698 y y' => @lem4806978 _110698 x r y y' s h1 h2 h3). Qed.
Lemma lem4806981 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4806982 {_110698 : Type'} (y : _110698) (y' : _110698) : (term508 _110698 y y') = (y = y').
Proof. exact (@lem4806981 (y = y')). Qed.
Lemma lem4806983 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (y : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : @IN _110698 y s) (h3 : @IN _110698 y' s) : y = y'.
Proof. exact (EQ_MP (@lem4806982 _110698 y y') (@lem4806979 _110698 x r y y' s h1 h2 h3)). Qed.
Lemma lem4806986 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4806988 {_110698 : Type'} (y : _110698) (y' : _110698) : (term22 _110698 y y') = (term509 _110698 y y').
Proof. exact (@lem4806986 (y = y')). Qed.
Lemma lem4806991 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : term509 _110698 y y'.
Proof. exact (EQ_MP (@lem4806988 _110698 y y') (@lem4804568 _110698 y y' x s r h1)). Qed.
Lemma lem4806994 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (y : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : @IN _110698 y s) (h3 : @IN _110698 y' s) : False.
Proof. exact (@lem4806991 _110698 y y' x s r h1 (@lem4806983 _110698 x r y y' s h1 h2 h3)). Qed.
Lemma lem4806995 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (y : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : @IN _110698 y s) (h3 : @IN _110698 y' s) : term454.
Proof. exact (fun h0 : ~ False => @lem4806994 _110698 x r y y' s h1 h2 h3). Qed.
Lemma lem4806997 (p : Prop) : (term403 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4806998 : term454 = False.
Proof. exact (@lem4806997 False). Qed.
Lemma lem4806999 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (y : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : @IN _110698 y s) (h3 : @IN _110698 y' s) : False.
Proof. exact (EQ_MP (@lem4806998) (@lem4806995 _110698 x r y y' s h1 h2 h3)). Qed.
Lemma lem4807000 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : (@IN _110698 y' s) = False.
Proof. exact (prop_ext (fun h4 : @IN _110698 y' s => @lem4806657 _110698 r y x y' s h1 h2 h3) (fun h4 : False => @lem4804938 _110698 y' s h3)). Qed.
Lemma lem4807002 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : False.
Proof. exact (EQ_MP (@lem4807000 _110698 r y x y' s h1 h2 h3) (@lem4804938 _110698 y' s h3)). Qed.
Lemma lem4807003 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (x : _110698) (y : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) (h3 : @IN _110698 y s) : (@IN _110698 y s) = False.
Proof. exact (prop_ext (fun h4 : @IN _110698 y s => @lem4806305 _110698 r y' x y s h1 h2 h3) (fun h4 : False => @lem4804842 _110698 y s h3)). Qed.
Lemma lem4807005 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (x : _110698) (y : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) (h3 : @IN _110698 y s) : False.
Proof. exact (EQ_MP (@lem4807003 _110698 r y' x y s h1 h2 h3) (@lem4804842 _110698 y s h3)). Qed.
Lemma lem4807006 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : y' = x) : False.
Proof. exact (EQ_MP (@lem4806086) (@lem4806083 _110698 s r y y' x h1 h2 h3)). Qed.
Lemma lem4807007 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : y' = x) : (y' = x) = False.
Proof. exact (prop_ext (fun h4 : y' = x => @lem4807006 _110698 s r y y' x h1 h2 h3) (fun h4 : False => @lem4804664 _110698 y' x h3)). Qed.
Lemma lem4807009 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : y' = x) : False.
Proof. exact (EQ_MP (@lem4807007 _110698 s r y y' x h1 h2 h3) (@lem4804664 _110698 y' x h3)). Qed.
Lemma lem4807010 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (y : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : @IN _110698 y s) (h3 : @IN _110698 y' s) : (@IN _110698 y s) = False.
Proof. exact (prop_ext (fun h4 : @IN _110698 y s => @lem4806999 _110698 x r y y' s h1 h2 h3) (fun h4 : False => @lem4804572 _110698 y s h2)). Qed.
Lemma lem4807011 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (y : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : @IN _110698 y s) (h3 : @IN _110698 y' s) : False.
Proof. exact (EQ_MP (@lem4807010 _110698 x r y y' s h1 h2 h3) (@lem4804572 _110698 y s h2)). Qed.
Lemma lem4807012 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (y : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : @IN _110698 y s) (h3 : @IN _110698 y' s) : (@IN _110698 y' s) = False.
Proof. exact (prop_ext (fun h4 : @IN _110698 y' s => @lem4807011 _110698 x r y y' s h1 h2 h3) (fun h4 : False => @lem4804570 _110698 y' s h3)). Qed.
Lemma lem4807013 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (y : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : @IN _110698 y s) (h3 : @IN _110698 y' s) : False.
Proof. exact (EQ_MP (@lem4807012 _110698 x r y y' s h1 h2 h3) (@lem4804570 _110698 y' s h3)). Qed.
Lemma lem4807014 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : (y = x) = False.
Proof. exact (prop_ext (fun h4 : y = x => @lem4807002 _110698 r y x y' s h1 h2 h3) (fun h4 : False => @lem4804522 _110698 y x h2)). Qed.
Lemma lem4807015 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : False.
Proof. exact (EQ_MP (@lem4807014 _110698 r y x y' s h1 h2 h3) (@lem4804522 _110698 y x h2)). Qed.
Lemma lem4807016 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : (@IN _110698 y' s) = False.
Proof. exact (prop_ext (fun h4 : @IN _110698 y' s => @lem4807015 _110698 r y x y' s h1 h2 h3) (fun h4 : False => @lem4804520 _110698 y' s h3)). Qed.
Lemma lem4807017 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : False.
Proof. exact (EQ_MP (@lem4807016 _110698 r y x y' s h1 h2 h3) (@lem4804520 _110698 y' s h3)). Qed.
Lemma lem4807018 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (x : _110698) (y : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) (h3 : @IN _110698 y s) : (@IN _110698 y s) = False.
Proof. exact (prop_ext (fun h4 : @IN _110698 y s => @lem4807005 _110698 r y' x y s h1 h2 h3) (fun h4 : False => @lem4804472 _110698 y s h3)). Qed.
Lemma lem4807019 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (x : _110698) (y : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) (h3 : @IN _110698 y s) : False.
Proof. exact (EQ_MP (@lem4807018 _110698 r y' x y s h1 h2 h3) (@lem4804472 _110698 y s h3)). Qed.
Lemma lem4807020 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (x : _110698) (y : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) (h3 : @IN _110698 y s) : (y' = x) = False.
Proof. exact (prop_ext (fun h4 : y' = x => @lem4807019 _110698 r y' x y s h1 h2 h3) (fun h4 : False => @lem4804470 _110698 y' x h2)). Qed.
Lemma lem4807021 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (x : _110698) (y : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) (h3 : @IN _110698 y s) : False.
Proof. exact (EQ_MP (@lem4807020 _110698 r y' x y s h1 h2 h3) (@lem4804470 _110698 y' x h2)). Qed.
Lemma lem4807022 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : y' = x) : (y = x) = False.
Proof. exact (prop_ext (fun h4 : y = x => @lem4807009 _110698 s r y y' x h1 h2 h3) (fun h4 : False => @lem4804422 _110698 y x h2)). Qed.
Lemma lem4807023 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : y' = x) : False.
Proof. exact (EQ_MP (@lem4807022 _110698 s r y y' x h1 h2 h3) (@lem4804422 _110698 y x h2)). Qed.
Lemma lem4807024 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : y' = x) : (y' = x) = False.
Proof. exact (prop_ext (fun h4 : y' = x => @lem4807023 _110698 s r y y' x h1 h2 h3) (fun h4 : False => @lem4804420 _110698 y' x h3)). Qed.
Lemma lem4807025 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : y' = x) : False.
Proof. exact (EQ_MP (@lem4807024 _110698 s r y y' x h1 h2 h3) (@lem4804420 _110698 y' x h3)). Qed.
Lemma lem4807026 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term359 _110698 r y x) (h2 : term247 _110698 x s r y y') (h3 : term118 _110698 s r y x) : (term359 _110698 r y x) = False.
Proof. exact (prop_ext (fun h4 : term359 _110698 r y x => @lem4805679 _110698 y' s r y x h1 h2 h3) (fun h4 : False => @lem4804244 _110698 r y x h1)). Qed.
Lemma lem4807027 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term359 _110698 r y x) (h2 : term247 _110698 x s r y y') (h3 : term118 _110698 s r y x) : False.
Proof. exact (EQ_MP (@lem4807026 _110698 y' s r y x h1 h2 h3) (@lem4804244 _110698 r y x h1)). Qed.
Lemma lem4807028 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term359 _110698 r x y) (h2 : term247 _110698 x s r y y') (h3 : term118 _110698 s r y x) : (term359 _110698 r x y) = False.
Proof. exact (prop_ext (fun h4 : term359 _110698 r x y => @lem4805337 _110698 y' s r y x h1 h2 h3) (fun h4 : False => @lem4804166 _110698 r x y h1)). Qed.
Lemma lem4807029 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term359 _110698 r x y) (h2 : term247 _110698 x s r y y') (h3 : term118 _110698 s r y x) : False.
Proof. exact (EQ_MP (@lem4807028 _110698 y' s r y x h1 h2 h3) (@lem4804166 _110698 r x y h1)). Qed.
Lemma lem4807030 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (y : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : @IN _110698 y s) (h3 : @IN _110698 y' s) : (@IN _110698 y s) = False.
Proof. exact (prop_ext (fun h4 : @IN _110698 y s => @lem4807013 _110698 x r y y' s h1 h2 h3) (fun h4 : False => @lem4804080 _110698 y s h2)). Qed.
Lemma lem4807031 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (y : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : @IN _110698 y s) (h3 : @IN _110698 y' s) : False.
Proof. exact (EQ_MP (@lem4807030 _110698 x r y y' s h1 h2 h3) (@lem4804080 _110698 y s h2)). Qed.
Lemma lem4807032 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (y : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : @IN _110698 y s) (h3 : @IN _110698 y' s) : (@IN _110698 y' s) = False.
Proof. exact (prop_ext (fun h4 : @IN _110698 y' s => @lem4807031 _110698 x r y y' s h1 h2 h3) (fun h4 : False => @lem4804076 _110698 y' s h3)). Qed.
Lemma lem4807033 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (y : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : @IN _110698 y s) (h3 : @IN _110698 y' s) : False.
Proof. exact (EQ_MP (@lem4807032 _110698 x r y y' s h1 h2 h3) (@lem4804076 _110698 y' s h3)). Qed.
Lemma lem4807034 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : (y = x) = False.
Proof. exact (prop_ext (fun h4 : y = x => @lem4807017 _110698 r y x y' s h1 h2 h3) (fun h4 : False => @lem4804007 _110698 y x h2)). Qed.
Lemma lem4807035 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : False.
Proof. exact (EQ_MP (@lem4807034 _110698 r y x y' s h1 h2 h3) (@lem4804007 _110698 y x h2)). Qed.
Lemma lem4807036 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : (@IN _110698 y' s) = False.
Proof. exact (prop_ext (fun h4 : @IN _110698 y' s => @lem4807035 _110698 r y x y' s h1 h2 h3) (fun h4 : False => @lem4804003 _110698 y' s h3)). Qed.
Lemma lem4807037 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : False.
Proof. exact (EQ_MP (@lem4807036 _110698 r y x y' s h1 h2 h3) (@lem4804003 _110698 y' s h3)). Qed.
Lemma lem4807038 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (x : _110698) (y : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) (h3 : @IN _110698 y s) : (@IN _110698 y s) = False.
Proof. exact (prop_ext (fun h4 : @IN _110698 y s => @lem4807021 _110698 r y' x y s h1 h2 h3) (fun h4 : False => @lem4803934 _110698 y s h3)). Qed.
Lemma lem4807039 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (x : _110698) (y : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) (h3 : @IN _110698 y s) : False.
Proof. exact (EQ_MP (@lem4807038 _110698 r y' x y s h1 h2 h3) (@lem4803934 _110698 y s h3)). Qed.
Lemma lem4807040 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (x : _110698) (y : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) (h3 : @IN _110698 y s) : (y' = x) = False.
Proof. exact (prop_ext (fun h4 : y' = x => @lem4807039 _110698 r y' x y s h1 h2 h3) (fun h4 : False => @lem4803930 _110698 y' x h2)). Qed.
Lemma lem4807041 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (x : _110698) (y : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) (h3 : @IN _110698 y s) : False.
Proof. exact (EQ_MP (@lem4807040 _110698 r y' x y s h1 h2 h3) (@lem4803930 _110698 y' x h2)). Qed.
Lemma lem4807042 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : y' = x) : (y = x) = False.
Proof. exact (prop_ext (fun h4 : y = x => @lem4807025 _110698 s r y y' x h1 h2 h3) (fun h4 : False => @lem4803861 _110698 y x h2)). Qed.
Lemma lem4807043 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : y' = x) : False.
Proof. exact (EQ_MP (@lem4807042 _110698 s r y y' x h1 h2 h3) (@lem4803861 _110698 y x h2)). Qed.
Lemma lem4807044 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : y' = x) : (y' = x) = False.
Proof. exact (prop_ext (fun h4 : y' = x => @lem4807043 _110698 s r y y' x h1 h2 h3) (fun h4 : False => @lem4803857 _110698 y' x h3)). Qed.
Lemma lem4807045 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : y' = x) : False.
Proof. exact (EQ_MP (@lem4807044 _110698 s r y y' x h1 h2 h3) (@lem4803857 _110698 y' x h3)). Qed.
Lemma lem4807046 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term359 _110698 r y x) (h2 : term247 _110698 x s r y y') (h3 : term118 _110698 s r y x) : (term359 _110698 r y x) = False.
Proof. exact (prop_ext (fun h4 : term359 _110698 r y x => @lem4807027 _110698 y' s r y x h1 h2 h3) (fun h4 : False => @lem4803694 _110698 r y x h1)). Qed.
Lemma lem4807047 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term359 _110698 r y x) (h2 : term247 _110698 x s r y y') (h3 : term118 _110698 s r y x) : False.
Proof. exact (EQ_MP (@lem4807046 _110698 y' s r y x h1 h2 h3) (@lem4803694 _110698 r y x h1)). Qed.
Lemma lem4807048 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term359 _110698 r x y) (h2 : term247 _110698 x s r y y') (h3 : term118 _110698 s r y x) : (term359 _110698 r x y) = False.
Proof. exact (prop_ext (fun h4 : term359 _110698 r x y => @lem4807029 _110698 y' s r y x h1 h2 h3) (fun h4 : False => @lem4803604 _110698 r x y h1)). Qed.
Lemma lem4807049 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term359 _110698 r x y) (h2 : term247 _110698 x s r y y') (h3 : term118 _110698 s r y x) : False.
Proof. exact (EQ_MP (@lem4807048 _110698 y' s r y x h1 h2 h3) (@lem4803604 _110698 r x y h1)). Qed.
Lemma lem4807050 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (y : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : @IN _110698 y s) (h3 : @IN _110698 y' s) : (@IN _110698 y s) = False.
Proof. exact (prop_ext (fun h4 : @IN _110698 y s => @lem4807033 _110698 x r y y' s h1 h2 h3) (fun h4 : False => @lem4804080 _110698 y s h2)). Qed.
Lemma lem4807051 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (y : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : @IN _110698 y s) (h3 : @IN _110698 y' s) : False.
Proof. exact (EQ_MP (@lem4807050 _110698 x r y y' s h1 h2 h3) (@lem4804080 _110698 y s h2)). Qed.
Lemma lem4807052 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (y : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : @IN _110698 y s) (h3 : @IN _110698 y' s) : (@IN _110698 y' s) = False.
Proof. exact (prop_ext (fun h4 : @IN _110698 y' s => @lem4807051 _110698 x r y y' s h1 h2 h3) (fun h4 : False => @lem4804076 _110698 y' s h3)). Qed.
Lemma lem4807053 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (y : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : @IN _110698 y s) (h3 : @IN _110698 y' s) : False.
Proof. exact (EQ_MP (@lem4807052 _110698 x r y y' s h1 h2 h3) (@lem4804076 _110698 y' s h3)). Qed.
Lemma lem4807054 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : (y = x) = False.
Proof. exact (prop_ext (fun h4 : y = x => @lem4807037 _110698 r y x y' s h1 h2 h3) (fun h4 : False => @lem4804007 _110698 y x h2)). Qed.
Lemma lem4807055 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : False.
Proof. exact (EQ_MP (@lem4807054 _110698 r y x y' s h1 h2 h3) (@lem4804007 _110698 y x h2)). Qed.
Lemma lem4807056 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : (@IN _110698 y' s) = False.
Proof. exact (prop_ext (fun h4 : @IN _110698 y' s => @lem4807055 _110698 r y x y' s h1 h2 h3) (fun h4 : False => @lem4804003 _110698 y' s h3)). Qed.
Lemma lem4807057 {_110698 : Type'} (r : type1402 _110698) (y : _110698) (x : _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : @IN _110698 y' s) : False.
Proof. exact (EQ_MP (@lem4807056 _110698 r y x y' s h1 h2 h3) (@lem4804003 _110698 y' s h3)). Qed.
Lemma lem4807058 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (x : _110698) (y : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) (h3 : @IN _110698 y s) : (@IN _110698 y s) = False.
Proof. exact (prop_ext (fun h4 : @IN _110698 y s => @lem4807041 _110698 r y' x y s h1 h2 h3) (fun h4 : False => @lem4803934 _110698 y s h3)). Qed.
Lemma lem4807059 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (x : _110698) (y : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) (h3 : @IN _110698 y s) : False.
Proof. exact (EQ_MP (@lem4807058 _110698 r y' x y s h1 h2 h3) (@lem4803934 _110698 y s h3)). Qed.
Lemma lem4807060 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (x : _110698) (y : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) (h3 : @IN _110698 y s) : (y' = x) = False.
Proof. exact (prop_ext (fun h4 : y' = x => @lem4807059 _110698 r y' x y s h1 h2 h3) (fun h4 : False => @lem4803930 _110698 y' x h2)). Qed.
Lemma lem4807061 {_110698 : Type'} (r : type1402 _110698) (y' : _110698) (x : _110698) (y : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) (h3 : @IN _110698 y s) : False.
Proof. exact (EQ_MP (@lem4807060 _110698 r y' x y s h1 h2 h3) (@lem4803930 _110698 y' x h2)). Qed.
Lemma lem4807062 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : y' = x) : (y = x) = False.
Proof. exact (prop_ext (fun h4 : y = x => @lem4807045 _110698 s r y y' x h1 h2 h3) (fun h4 : False => @lem4803861 _110698 y x h2)). Qed.
Lemma lem4807063 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : y' = x) : False.
Proof. exact (EQ_MP (@lem4807062 _110698 s r y y' x h1 h2 h3) (@lem4803861 _110698 y x h2)). Qed.
Lemma lem4807064 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : y' = x) : (y' = x) = False.
Proof. exact (prop_ext (fun h4 : y' = x => @lem4807063 _110698 s r y y' x h1 h2 h3) (fun h4 : False => @lem4803857 _110698 y' x h3)). Qed.
Lemma lem4807065 {_110698 : Type'} (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y = x) (h3 : y' = x) : False.
Proof. exact (EQ_MP (@lem4807064 _110698 s r y y' x h1 h2 h3) (@lem4803857 _110698 y' x h3)). Qed.
Lemma lem4807066 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term359 _110698 r y x) (h2 : term247 _110698 x s r y y') (h3 : term118 _110698 s r y x) : (term359 _110698 r y x) = False.
Proof. exact (prop_ext (fun h4 : term359 _110698 r y x => @lem4807047 _110698 y' s r y x h1 h2 h3) (fun h4 : False => @lem4803694 _110698 r y x h1)). Qed.
Lemma lem4807067 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term359 _110698 r y x) (h2 : term247 _110698 x s r y y') (h3 : term118 _110698 s r y x) : False.
Proof. exact (EQ_MP (@lem4807066 _110698 y' s r y x h1 h2 h3) (@lem4803694 _110698 r y x h1)). Qed.
Lemma lem4807068 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term359 _110698 r x y) (h2 : term247 _110698 x s r y y') (h3 : term118 _110698 s r y x) : (term359 _110698 r x y) = False.
Proof. exact (prop_ext (fun h4 : term359 _110698 r x y => @lem4807049 _110698 y' s r y x h1 h2 h3) (fun h4 : False => @lem4803604 _110698 r x y h1)). Qed.
Lemma lem4807069 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term359 _110698 r x y) (h2 : term247 _110698 x s r y y') (h3 : term118 _110698 s r y x) : False.
Proof. exact (EQ_MP (@lem4807068 _110698 y' s r y x h1 h2 h3) (@lem4803604 _110698 r x y h1)). Qed.
Lemma lem4807070 {_110698 : Type'} (y : _110698) (x : _110698) (r : type1402 _110698) (y' : _110698) (s : _110698 -> Prop) (h1 : term282 _110698 y y' x s r) (h2 : @IN _110698 y' s) : False.
Proof. exact (or_elim (@lem4803506 _110698 y y' x s r h1) (fun h0 : y = x => @lem4807057 _110698 r y x y' s h1 h0 h2) (fun h0 : @IN _110698 y s => @lem4807053 _110698 x r y y' s h1 h0 h2)). Qed.
Lemma lem4807071 {_110698 : Type'} (y : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y' : _110698) (x : _110698) (h1 : term282 _110698 y y' x s r) (h2 : y' = x) : False.
Proof. exact (or_elim (@lem4803506 _110698 y y' x s r h1) (fun h0 : y = x => @lem4807065 _110698 s r y y' x h1 h0 h2) (fun h0 : @IN _110698 y s => @lem4807061 _110698 r y' x y s h1 h2 h0)). Qed.
Lemma lem4807072 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term282 _110698 y y' x s r) : False.
Proof. exact (or_elim (@lem4803508 _110698 y y' x s r h1) (fun h0 : y' = x => @lem4807071 _110698 y s r y' x h1 h0) (fun h0 : @IN _110698 y' s => @lem4807070 _110698 y x r y' s h1 h0)). Qed.
Lemma lem4807073 {_110698 : Type'} (y' : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (x : _110698) (h1 : term247 _110698 x s r y y') (h2 : term118 _110698 s r y x) : False.
Proof. exact (or_elim (@lem4803487 _110698 s r y x h2) (fun h0 : term359 _110698 r x y => @lem4807069 _110698 y' s r y x h0 h1 h2) (fun h0 : term359 _110698 r y x => @lem4807067 _110698 y' s r y x h0 h1 h2)). Qed.
Lemma lem4807074 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (y : _110698) (y' : _110698) (h1 : term247 _110698 x s r y y') : False.
Proof. exact (or_elim (@lem4803483 _110698 x s r y y' h1) (fun h0 : term118 _110698 s r y x => @lem4807073 _110698 y' s r y x h1 h0) (fun h0 : term142 _110698 s r y y' => @lem4806021 _110698 x s r y y' h1 h0)). Qed.
Lemma lem4807075 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term324 _110698 y y' x s r) : False.
Proof. exact (or_elim (@lem4803480 _110698 y y' x s r h1) (fun h0 : term247 _110698 x s r y y' => @lem4807074 _110698 x s r y y' h0) (fun h0 : term282 _110698 y y' x s r => @lem4807072 _110698 y y' x s r h0)). Qed.
Lemma lem4807076 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term324 _110698 y y' x s r) : (term324 _110698 y y' x s r) = False.
Proof. exact (prop_ext (fun h2 : term324 _110698 y y' x s r => @lem4807075 _110698 y y' x s r h1) (fun h2 : False => @lem4803480 _110698 y y' x s r h1)). Qed.
Lemma lem4807077 {_110698 : Type'} (y : _110698) (y' : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term324 _110698 y y' x s r) : False.
Proof. exact (EQ_MP (@lem4807076 _110698 y y' x s r h1) (@lem4803480 _110698 y y' x s r h1)). Qed.
Lemma lem4807078 {_110698 : Type'} (y : _110698) (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term327 _110698 y x s r) : False.
Proof. exact (ex_elim (@lem4803214 _110698 y x s r h1) (fun y' : _110698 => fun h0 : term326 _110698 y x s r y' => @lem4807077 _110698 y y' x s r h0)). Qed.
Lemma lem4807079 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term71 _110698 x s r) : False.
Proof. exact (ex_elim (@lem4803213 _110698 x s r h1) (fun y : _110698 => fun h0 : term328 _110698 x s r y => @lem4807078 _110698 y x s r h0)). Qed.
Lemma lem4807080 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term71 _110698 x s r) : (term71 _110698 x s r) = False.
Proof. exact (prop_ext (fun h2 : term71 _110698 x s r => @lem4807079 _110698 x s r h1) (fun h2 : False => @lem4802453 _110698 x s r h1)). Qed.
Lemma lem4807081 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) (h1 : term71 _110698 x s r) : False.
Proof. exact (EQ_MP (@lem4807080 _110698 x s r h1) (@lem4802453 _110698 x s r h1)). Qed.
Lemma lem4807082 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : term70 _110698 x s r.
Proof. exact (fun h0 : term71 _110698 x s r => @lem4807081 _110698 x s r h0). Qed.
Lemma lem4807083 {_110698 : Type'} (x : _110698) (s : _110698 -> Prop) (r : type1402 _110698) : (term37 _110698 x s r) = (term42 _110698 x s r).
Proof. exact (EQ_MP (@lem4802452 _110698 x s r) (@lem4807082 _110698 x s r)). Qed.
Lemma lem4807088 {_110698 : Type'} (x : _110698) (r : type1402 _110698) : term46 _110698 x r.
Proof. exact (fun s : _110698 -> Prop => @lem4807083 _110698 x s r). Qed.
Lemma lem4807093 {_110698 : Type'} (r : type1402 _110698) : term50 _110698 r.
Proof. exact (fun x : _110698 => @lem4807088 _110698 x r). Qed.
Lemma lem4807098 {_110698 : Type'} : term54 _110698.
Proof. exact (fun r : type1402 _110698 => @lem4807093 _110698 r). Qed.
Lemma lem4807099 {_110698 : Type'} : term56 _110698.
Proof. exact (EQ_MP (@lem4802448 _110698) (@lem4807098 _110698)). Qed.
Lemma lem4807101 {_110698 : Type'} : term56 _110698.
Proof. exact (@lem4802222 _110698 (@lem4807099 _110698)). Qed.
Lemma lem4807102 {_110698 : Type'} (h1 : term57 _110698) : False.
Proof. exact (@lem4807101 _110698 (@lem4802206 _110698 h1)). Qed.
Lemma lem4807103 {_110698 : Type'} (h1 : term57 _110698) : (term57 _110698) = False.
Proof. exact (prop_ext (fun h2 : term57 _110698 => @lem4807102 _110698 h1) (fun h2 : False => @lem4802206 _110698 h1)). Qed.
Lemma lem4807104 {_110698 : Type'} (h1 : term57 _110698) : False.
Proof. exact (EQ_MP (@lem4807103 _110698 h1) (@lem4802206 _110698 h1)). Qed.
Lemma lem4807105 {_110698 : Type'} : term56 _110698.
Proof. exact (fun h0 : term57 _110698 => @lem4807104 _110698 h0). Qed.
Lemma lem4807106 {_110698 : Type'} : term54 _110698.
Proof. exact (EQ_MP (@lem4802205 _110698) (@lem4807105 _110698)). Qed.
Lemma lem4807107 {_110698 : Type'} : term53 _110698.
Proof. exact (EQ_MP (@lem4802201 _110698) (@lem4807106 _110698)). Qed.
