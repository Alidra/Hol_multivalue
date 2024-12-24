Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINREC_1_LEMMA_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16433_spec.
Require Import thm16434_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm17930_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1857_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm3791009_spec.
Require Import thm3791010_spec.
Require Import thm3791024_spec.
Require Import thm3791025_spec.
Lemma lem3791028 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3791029 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3791030 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3791029 t1) (@lem3791028 t1)). Qed.
Lemma lem3791031 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3791030 t1 t2). Qed.
Lemma lem3791032 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3791033 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3791032 t1 t2) (@lem3791031 t1 t2)). Qed.
Lemma lem3791034 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3791033 t1 t2 t3). Qed.
Lemma lem3791035 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3791036 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3791035 t1 t2 t3) (@lem3791034 t1 t2 t3)). Qed.
Lemma lem3791037 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3791036 t1 t2 t3)). Qed.
Lemma lem3791059 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) : (term7 A B f b s a n) = (term8 A B b s n a f).
Proof. exact (EQ_MP (@lem3791025 A B b s n a f) (@lem3791024 A B b s n a f)). Qed.
Lemma lem3791060 {_98584 _98585 : Type'} (b : _98584) (s : _98585 -> Prop) (n : nat) (a : _98584) (f : type1467 _98584 _98585) : (term9 _98584 _98585 f b s a n) = (term10 _98584 _98585 b s n a f).
Proof. exact (@lem3791059 _98585 _98584 b s n a f). Qed.
Lemma lem3791061 {_98584 _98585 : Type'} (b : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) : (term11 _98584 _98585 f b s a) = (term12 _98584 _98585 b s a f).
Proof. exact (@lem3791060 _98584 _98585 b s (NUMERAL 0) a f). Qed.
Lemma lem3791075 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) : (term13 A B f b s a) = (term14 A B s a b).
Proof. exact (EQ_MP (@lem3791010 A B f s a b) (@lem3791009 A B f s a b)). Qed.
Lemma lem3791076 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (s : _98585 -> Prop) (a : _98584) (b : _98584) : (term15 _98584 _98585 f b s a) = (term16 _98584 _98585 s a b).
Proof. exact (@lem3791075 _98585 _98584 f s a b). Qed.
Lemma lem3791077 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term17 _98584 _98585 f b s x c) = (term18 _98584 _98585 s x c b).
Proof. exact (@lem3791076 _98584 _98585 f (@DELETE _98585 s x) c b). Qed.
Lemma lem3791084 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3791085 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term19 _98584 _98585 f b s x c) = (term20 _98584 _98585 s x c b).
Proof. exact (MK_COMB (@lem3791084) (@lem3791077 _98584 _98585 f s x c b)). Qed.
Lemma lem3791088 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (a = (f x c)) = (a = (f x c)).
Proof. exact (eq_refl (a = (f x c))). Qed.
Lemma lem3791089 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term21 _98584 _98585 b s a f x c) = (term22 _98584 _98585 s b a f x c).
Proof. exact (MK_COMB (@lem3791085 _98584 _98585 f s x c b) (@lem3791088 _98584 _98585 a f x c)). Qed.
Lemma lem3791092 {_98585 : Type'} (x : _98585) (s : _98585 -> Prop) : (term23 _98585 x s) = (term23 _98585 x s).
Proof. exact (eq_refl (term23 _98585 x s)). Qed.
Lemma lem3791093 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term24 _98584 _98585 b s a f x c) = (term25 _98584 _98585 s b a f x c).
Proof. exact (MK_COMB (@lem3791092 _98585 x s) (@lem3791089 _98584 _98585 s b a f x c)). Qed.
Lemma lem3791096 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term26 _98584 _98585 b s a f x) = (term27 _98584 _98585 s b a f x).
Proof. exact (fun_ext (fun c : _98584 => @lem3791093 _98584 _98585 s b a f x c)). Qed.
Lemma lem3791097 {_98584 : Type'} : (@ex _98584) = (@ex _98584).
Proof. exact (eq_refl (@ex _98584)). Qed.
Lemma lem3791098 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term28 _98584 _98585 b s a f x) = (term29 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3791097 _98584) (@lem3791096 _98584 _98585 s b a f x)). Qed.
Lemma lem3791103 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) : (term30 _98584 _98585 b s a f) = (term31 _98584 _98585 s b a f).
Proof. exact (fun_ext (fun x : _98585 => @lem3791098 _98584 _98585 s b a f x)). Qed.
Lemma lem3791104 {_98585 : Type'} : (@ex _98585) = (@ex _98585).
Proof. exact (eq_refl (@ex _98585)). Qed.
Lemma lem3791105 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) : (term12 _98584 _98585 b s a f) = (term32 _98584 _98585 s b a f).
Proof. exact (MK_COMB (@lem3791104 _98585) (@lem3791103 _98584 _98585 s b a f)). Qed.
Lemma lem3791110 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) : (term11 _98584 _98585 f b s a) = (term32 _98584 _98585 s b a f).
Proof. exact (TRANS (@lem3791061 _98584 _98585 b s a f) (@lem3791105 _98584 _98585 s b a f)). Qed.
Lemma lem3791111 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3791112 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) : (term33 _98584 _98585 f b s a) = (term34 _98584 _98585 s b a f).
Proof. exact (MK_COMB (@lem3791111) (@lem3791110 _98584 _98585 s b a f)). Qed.
Lemma lem3791123 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) : (term35 _98584 _98585 s a f b) = (term35 _98584 _98585 s a f b).
Proof. exact (eq_refl (term35 _98584 _98585 s a f b)). Qed.
Lemma lem3791124 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) : ((term11 _98584 _98585 f b s a) = (term35 _98584 _98585 s a f b)) = ((term32 _98584 _98585 s b a f) = (term35 _98584 _98585 s a f b)).
Proof. exact (MK_COMB (@lem3791112 _98584 _98585 s b a f) (@lem3791123 _98584 _98585 s a f b)). Qed.
Lemma lem3791127 {_98584 _98585 : Type'} (s : _98585 -> Prop) (f : type1467 _98584 _98585) (b : _98584) : (term36 _98584 _98585 s f b) = (term37 _98584 _98585 s f b).
Proof. exact (fun_ext (fun a : _98584 => @lem3791124 _98584 _98585 s a f b)). Qed.
Lemma lem3791128 {_98584 : Type'} : (@all _98584) = (@all _98584).
Proof. exact (eq_refl (@all _98584)). Qed.
Lemma lem3791129 {_98584 _98585 : Type'} (s : _98585 -> Prop) (f : type1467 _98584 _98585) (b : _98584) : (term38 _98584 _98585 s f b) = (term39 _98584 _98585 s f b).
Proof. exact (MK_COMB (@lem3791128 _98584) (@lem3791127 _98584 _98585 s f b)). Qed.
Lemma lem3791134 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (b : _98584) : (term40 _98584 _98585 f b) = (term41 _98584 _98585 f b).
Proof. exact (fun_ext (fun s : _98585 -> Prop => @lem3791129 _98584 _98585 s f b)). Qed.
Lemma lem3791135 {_98585 : Type'} : (@all (_98585 -> Prop)) = (@all (_98585 -> Prop)).
Proof. exact (eq_refl (@all (_98585 -> Prop))). Qed.
Lemma lem3791136 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (b : _98584) : (term42 _98584 _98585 f b) = (term43 _98584 _98585 f b).
Proof. exact (MK_COMB (@lem3791135 _98585) (@lem3791134 _98584 _98585 f b)). Qed.
Lemma lem3791141 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) : (term44 _98584 _98585 f) = (term45 _98584 _98585 f).
Proof. exact (fun_ext (fun b : _98584 => @lem3791136 _98584 _98585 f b)). Qed.
Lemma lem3791142 {_98584 : Type'} : (@all _98584) = (@all _98584).
Proof. exact (eq_refl (@all _98584)). Qed.
Lemma lem3791143 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) : (term46 _98584 _98585 f) = (term47 _98584 _98585 f).
Proof. exact (MK_COMB (@lem3791142 _98584) (@lem3791141 _98584 _98585 f)). Qed.
Lemma lem3791148 {_98584 _98585 : Type'} : (term48 _98584 _98585) = (term49 _98584 _98585).
Proof. exact (fun_ext (fun f : type1467 _98584 _98585 => @lem3791143 _98584 _98585 f)). Qed.
Lemma lem3791149 {_98584 _98585 : Type'} : (@all (_98585 -> _98584 -> _98584)) = (@all (_98585 -> _98584 -> _98584)).
Proof. exact (eq_refl (@all (_98585 -> _98584 -> _98584))). Qed.
Lemma lem3791150 {_98584 _98585 : Type'} : (term50 _98584 _98585) = (term51 _98584 _98585).
Proof. exact (MK_COMB (@lem3791149 _98584 _98585) (@lem3791148 _98584 _98585)). Qed.
Lemma lem3791155 {_98584 _98585 : Type'} : (term51 _98584 _98585) = (term50 _98584 _98585).
Proof. exact (SYM (@lem3791150 _98584 _98585)). Qed.
Lemma lem3791156 {_98585 : Type'} : (@ex _98585) = (@ex _98585).
Proof. exact (eq_refl (@ex _98585)). Qed.
Lemma lem3791174 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term52 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3791175 {_98585 : Type'} (s : _98585 -> Prop) (t : _98585 -> Prop) : (s = t) = (term52 _98585 s t).
Proof. exact (@lem3791174 _98585 s t). Qed.
Lemma lem3791176 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : ((@DELETE _98585 s x) = (@EMPTY _98585)) = (term53 _98585 s x).
Proof. exact (@lem3791175 _98585 (@DELETE _98585 s x) (@EMPTY _98585)). Qed.
Lemma lem3791185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3791186 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term54 _98585 s x) = (term55 _98585 s x).
Proof. exact (MK_COMB (@lem3791185) (@lem3791176 _98585 s x)). Qed.
Lemma lem3791191 {_98584 : Type'} (c : _98584) (b : _98584) : (c = b) = (c = b).
Proof. exact (eq_refl (c = b)). Qed.
Lemma lem3791192 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term18 _98584 _98585 s x c b) = (term56 _98584 _98585 s x c b).
Proof. exact (MK_COMB (@lem3791186 _98585 s x) (@lem3791191 _98584 c b)). Qed.
Lemma lem3791195 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3791196 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term20 _98584 _98585 s x c b) = (term57 _98584 _98585 s x c b).
Proof. exact (MK_COMB (@lem3791195) (@lem3791192 _98584 _98585 s x c b)). Qed.
Lemma lem3791201 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (a = (f x c)) = (a = (f x c)).
Proof. exact (eq_refl (a = (f x c))). Qed.
Lemma lem3791202 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term22 _98584 _98585 s b a f x c) = (term58 _98584 _98585 s b a f x c).
Proof. exact (MK_COMB (@lem3791196 _98584 _98585 s x c b) (@lem3791201 _98584 _98585 a f x c)). Qed.
Lemma lem3791205 {_98585 : Type'} (x : _98585) (s : _98585 -> Prop) : (term23 _98585 x s) = (term23 _98585 x s).
Proof. exact (eq_refl (term23 _98585 x s)). Qed.
Lemma lem3791206 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term25 _98584 _98585 s b a f x c) = (term59 _98584 _98585 s b a f x c).
Proof. exact (MK_COMB (@lem3791205 _98585 x s) (@lem3791202 _98584 _98585 s b a f x c)). Qed.
Lemma lem3791209 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term27 _98584 _98585 s b a f x) = (term60 _98584 _98585 s b a f x).
Proof. exact (fun_ext (fun c : _98584 => @lem3791206 _98584 _98585 s b a f x c)). Qed.
Lemma lem3791210 {_98584 : Type'} : (@ex _98584) = (@ex _98584).
Proof. exact (eq_refl (@ex _98584)). Qed.
Lemma lem3791211 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term29 _98584 _98585 s b a f x) = (term61 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3791210 _98584) (@lem3791209 _98584 _98585 s b a f x)). Qed.
Lemma lem3791216 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3791217 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term62 _98584 _98585 s b a f x) = (term63 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3791216) (@lem3791211 _98584 _98585 s b a f x)). Qed.
Lemma lem3791223 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term52 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3791224 {_98585 : Type'} (s : _98585 -> Prop) (t : _98585 -> Prop) : (s = t) = (term52 _98585 s t).
Proof. exact (@lem3791223 _98585 s t). Qed.
Lemma lem3791225 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (s = (@INSERT _98585 x (@EMPTY _98585))) = (term64 _98585 s x).
Proof. exact (@lem3791224 _98585 s (@INSERT _98585 x (@EMPTY _98585))). Qed.
Lemma lem3791234 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3791235 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term65 _98585 s x) = (term66 _98585 s x).
Proof. exact (MK_COMB (@lem3791234) (@lem3791225 _98585 s x)). Qed.
Lemma lem3791240 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (a = (f x b)) = (a = (f x b)).
Proof. exact (eq_refl (a = (f x b))). Qed.
Lemma lem3791241 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term67 _98584 _98585 s a f x b) = (term68 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3791235 _98585 s x) (@lem3791240 _98584 _98585 a f x b)). Qed.
Lemma lem3791244 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : ((term29 _98584 _98585 s b a f x) = (term67 _98584 _98585 s a f x b)) = ((term61 _98584 _98585 s b a f x) = (term68 _98584 _98585 s a f x b)).
Proof. exact (MK_COMB (@lem3791217 _98584 _98585 s b a f x) (@lem3791241 _98584 _98585 s a f x b)). Qed.
Lemma lem3791249 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : ((term61 _98584 _98585 s b a f x) = (term68 _98584 _98585 s a f x b)) = ((term29 _98584 _98585 s b a f x) = (term67 _98584 _98585 s a f x b)).
Proof. exact (SYM (@lem3791244 _98584 _98585 s a f x b)). Qed.
Lemma lem3791259 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3791260 {_98585 : Type'} (P : _98585 -> Prop) (x : _98585) : (@IN _98585 x P) = (P x).
Proof. exact (@lem3791259 _98585 P x). Qed.
Lemma lem3791261 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (@IN _98585 x s) = (s x).
Proof. exact (@lem3791260 _98585 s x). Qed.
Lemma lem3791262 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3791263 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term23 _98585 x s) = (term69 _98585 s x).
Proof. exact (MK_COMB (@lem3791262) (@lem3791261 _98585 s x)). Qed.
Lemma lem3791275 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term70 A x s y) = (term71 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3791276 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) (y : _98585) : (term70 _98585 x s y) = (term71 _98585 s x y).
Proof. exact (@lem3791275 _98585 s x y). Qed.
Lemma lem3791277 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term70 _98585 x' s x) = (term71 _98585 s x' x).
Proof. exact (@lem3791276 _98585 s x' x). Qed.
Lemma lem3791281 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3791282 {_98585 : Type'} (P : _98585 -> Prop) (x : _98585) : (@IN _98585 x P) = (P x).
Proof. exact (@lem3791281 _98585 P x). Qed.
Lemma lem3791283 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) : (@IN _98585 x' s) = (s x').
Proof. exact (@lem3791282 _98585 s x'). Qed.
Lemma lem3791284 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3791285 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) : (term23 _98585 x' s) = (term69 _98585 s x').
Proof. exact (MK_COMB (@lem3791284) (@lem3791283 _98585 s x')). Qed.
Lemma lem3791288 {_98585 : Type'} (x' : _98585) (x : _98585) : (term72 _98585 x' x) = (term72 _98585 x' x).
Proof. exact (eq_refl (term72 _98585 x' x)). Qed.
Lemma lem3791289 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term71 _98585 s x' x) = (term73 _98585 s x' x).
Proof. exact (MK_COMB (@lem3791285 _98585 s x') (@lem3791288 _98585 x' x)). Qed.
Lemma lem3791292 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term70 _98585 x' s x) = (term73 _98585 s x' x).
Proof. exact (TRANS (@lem3791277 _98585 s x' x) (@lem3791289 _98585 s x' x)). Qed.
Lemma lem3791293 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3791294 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term74 _98585 x' s x) = (term75 _98585 s x' x).
Proof. exact (MK_COMB (@lem3791293) (@lem3791292 _98585 s x' x)). Qed.
Lemma lem3791296 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3791297 {_98585 : Type'} (x : _98585) : (@IN _98585 x (@EMPTY _98585)) = False.
Proof. exact (@lem3791296 _98585 x). Qed.
Lemma lem3791298 {_98585 : Type'} (x' : _98585) : (@IN _98585 x' (@EMPTY _98585)) = False.
Proof. exact (@lem3791297 _98585 x'). Qed.
Lemma lem3791299 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : ((term70 _98585 x' s x) = (@IN _98585 x' (@EMPTY _98585))) = ((term73 _98585 s x' x) = False).
Proof. exact (MK_COMB (@lem3791294 _98585 s x' x) (@lem3791298 _98585 x')). Qed.
Lemma lem3791301 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3791302 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : ((term73 _98585 s x' x) = False) = (term76 _98585 s x' x).
Proof. exact (@lem3791301 (term73 _98585 s x' x)). Qed.
Lemma lem3791307 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : ((term70 _98585 x' s x) = (@IN _98585 x' (@EMPTY _98585))) = (term76 _98585 s x' x).
Proof. exact (TRANS (@lem3791299 _98585 s x' x) (@lem3791302 _98585 s x' x)). Qed.
Lemma lem3791308 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term77 _98585 s x) = (term78 _98585 s x).
Proof. exact (fun_ext (fun x' : _98585 => @lem3791307 _98585 s x' x)). Qed.
Lemma lem3791309 {_98585 : Type'} : (@all _98585) = (@all _98585).
Proof. exact (eq_refl (@all _98585)). Qed.
Lemma lem3791310 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term53 _98585 s x) = (term79 _98585 s x).
Proof. exact (MK_COMB (@lem3791309 _98585) (@lem3791308 _98585 s x)). Qed.
Lemma lem3791315 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3791316 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term55 _98585 s x) = (term80 _98585 s x).
Proof. exact (MK_COMB (@lem3791315) (@lem3791310 _98585 s x)). Qed.
Lemma lem3791319 {_98584 : Type'} (c : _98584) (b : _98584) : (c = b) = (c = b).
Proof. exact (eq_refl (c = b)). Qed.
Lemma lem3791320 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term56 _98584 _98585 s x c b) = (term81 _98584 _98585 s x c b).
Proof. exact (MK_COMB (@lem3791316 _98585 s x) (@lem3791319 _98584 c b)). Qed.
Lemma lem3791323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3791324 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term57 _98584 _98585 s x c b) = (term82 _98584 _98585 s x c b).
Proof. exact (MK_COMB (@lem3791323) (@lem3791320 _98584 _98585 s x c b)). Qed.
Lemma lem3791327 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (a = (f x c)) = (a = (f x c)).
Proof. exact (eq_refl (a = (f x c))). Qed.
Lemma lem3791328 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term58 _98584 _98585 s b a f x c) = (term83 _98584 _98585 s b a f x c).
Proof. exact (MK_COMB (@lem3791324 _98584 _98585 s x c b) (@lem3791327 _98584 _98585 a f x c)). Qed.
Lemma lem3791331 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term59 _98584 _98585 s b a f x c) = (term84 _98584 _98585 s b a f x c).
Proof. exact (MK_COMB (@lem3791263 _98585 s x) (@lem3791328 _98584 _98585 s b a f x c)). Qed.
Lemma lem3791334 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term60 _98584 _98585 s b a f x) = (term85 _98584 _98585 s b a f x).
Proof. exact (fun_ext (fun c : _98584 => @lem3791331 _98584 _98585 s b a f x c)). Qed.
Lemma lem3791335 {_98584 : Type'} : (@ex _98584) = (@ex _98584).
Proof. exact (eq_refl (@ex _98584)). Qed.
Lemma lem3791336 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term61 _98584 _98585 s b a f x) = (term86 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3791335 _98584) (@lem3791334 _98584 _98585 s b a f x)). Qed.
Lemma lem3791341 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3791342 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term63 _98584 _98585 s b a f x) = (term87 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3791341) (@lem3791336 _98584 _98585 s b a f x)). Qed.
Lemma lem3791352 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3791353 {_98585 : Type'} (P : _98585 -> Prop) (x : _98585) : (@IN _98585 x P) = (P x).
Proof. exact (@lem3791352 _98585 P x). Qed.
Lemma lem3791354 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) : (@IN _98585 x' s) = (s x').
Proof. exact (@lem3791353 _98585 s x'). Qed.
Lemma lem3791355 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3791356 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) : (term88 _98585 x' s) = (term89 _98585 s x').
Proof. exact (MK_COMB (@lem3791355) (@lem3791354 _98585 s x')). Qed.
Lemma lem3791358 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term90 A x y s) = (term91 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3791359 {_98585 : Type'} (y : _98585) (x : _98585) (s : _98585 -> Prop) : (term90 _98585 x y s) = (term91 _98585 y x s).
Proof. exact (@lem3791358 _98585 y x s). Qed.
Lemma lem3791360 {_98585 : Type'} (x : _98585) (x' : _98585) : (term92 _98585 x' x) = (term93 _98585 x x').
Proof. exact (@lem3791359 _98585 x x' (@EMPTY _98585)). Qed.
Lemma lem3791366 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3791367 {_98585 : Type'} (x : _98585) : (@IN _98585 x (@EMPTY _98585)) = False.
Proof. exact (@lem3791366 _98585 x). Qed.
Lemma lem3791368 {_98585 : Type'} (x' : _98585) : (@IN _98585 x' (@EMPTY _98585)) = False.
Proof. exact (@lem3791367 _98585 x'). Qed.
Lemma lem3791369 {_98585 : Type'} (x' : _98585) (x : _98585) : (term94 _98585 x' x) = (term94 _98585 x' x).
Proof. exact (eq_refl (term94 _98585 x' x)). Qed.
Lemma lem3791370 {_98585 : Type'} (x' : _98585) (x : _98585) : (term93 _98585 x x') = (term95 _98585 x' x).
Proof. exact (MK_COMB (@lem3791369 _98585 x' x) (@lem3791368 _98585 x')). Qed.
Lemma lem3791372 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3791373 {_98585 : Type'} (x' : _98585) (x : _98585) : (term95 _98585 x' x) = (x' = x).
Proof. exact (@lem3791372 (x' = x)). Qed.
Lemma lem3791376 {_98585 : Type'} (x' : _98585) (x : _98585) : (term93 _98585 x x') = (x' = x).
Proof. exact (TRANS (@lem3791370 _98585 x' x) (@lem3791373 _98585 x' x)). Qed.
Lemma lem3791377 {_98585 : Type'} (x' : _98585) (x : _98585) : (term92 _98585 x' x) = (x' = x).
Proof. exact (TRANS (@lem3791360 _98585 x x') (@lem3791376 _98585 x' x)). Qed.
Lemma lem3791378 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : ((@IN _98585 x' s) = (term92 _98585 x' x)) = ((s x') = (x' = x)).
Proof. exact (MK_COMB (@lem3791356 _98585 s x') (@lem3791377 _98585 x' x)). Qed.
Lemma lem3791381 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term96 _98585 s x) = (term97 _98585 s x).
Proof. exact (fun_ext (fun x' : _98585 => @lem3791378 _98585 s x' x)). Qed.
Lemma lem3791382 {_98585 : Type'} : (@all _98585) = (@all _98585).
Proof. exact (eq_refl (@all _98585)). Qed.
Lemma lem3791383 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term64 _98585 s x) = (term98 _98585 s x).
Proof. exact (MK_COMB (@lem3791382 _98585) (@lem3791381 _98585 s x)). Qed.
Lemma lem3791388 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3791389 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term66 _98585 s x) = (term99 _98585 s x).
Proof. exact (MK_COMB (@lem3791388) (@lem3791383 _98585 s x)). Qed.
Lemma lem3791392 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (a = (f x b)) = (a = (f x b)).
Proof. exact (eq_refl (a = (f x b))). Qed.
Lemma lem3791393 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term68 _98584 _98585 s a f x b) = (term100 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3791389 _98585 s x) (@lem3791392 _98584 _98585 a f x b)). Qed.
Lemma lem3791396 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : ((term61 _98584 _98585 s b a f x) = (term68 _98584 _98585 s a f x b)) = ((term86 _98584 _98585 s b a f x) = (term100 _98584 _98585 s a f x b)).
Proof. exact (MK_COMB (@lem3791342 _98584 _98585 s b a f x) (@lem3791393 _98584 _98585 s a f x b)). Qed.
Lemma lem3791399 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : ((term86 _98584 _98585 s b a f x) = (term100 _98584 _98585 s a f x b)) = ((term61 _98584 _98585 s b a f x) = (term68 _98584 _98585 s a f x b)).
Proof. exact (SYM (@lem3791396 _98584 _98585 s a f x b)). Qed.
Lemma lem3791401 (p : Prop) : p = (term101 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3791402 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : ((term86 _98584 _98585 s b a f x) = (term100 _98584 _98585 s a f x b)) = (term102 _98584 _98585 s a f x b).
Proof. exact (@lem3791401 ((term86 _98584 _98585 s b a f x) = (term100 _98584 _98585 s a f x b))). Qed.
Lemma lem3791403 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term102 _98584 _98585 s a f x b) = ((term86 _98584 _98585 s b a f x) = (term100 _98584 _98585 s a f x b)).
Proof. exact (SYM (@lem3791402 _98584 _98585 s a f x b)). Qed.
Lemma lem3791404 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term103 _98584 _98585 s a f x b) : term103 _98584 _98585 s a f x b.
Proof. exact (h1). Qed.
Lemma lem3791407 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term102 _98584 _98585 s a f x b) : term102 _98584 _98585 s a f x b.
Proof. exact (h1). Qed.
Lemma lem3791408 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : term104 _98584 _98585 s a f x b.
Proof. exact (fun h0 : term102 _98584 _98585 s a f x b => @lem3791407 _98584 _98585 s a f x b h0). Qed.
Lemma lem3791409 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term104 _98584 _98585 s a f x b) : term104 _98584 _98585 s a f x b.
Proof. exact (h1). Qed.
Lemma lem3791410 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term102 _98584 _98585 s a f x b) : term102 _98584 _98585 s a f x b.
Proof. exact (h1). Qed.
Lemma lem3791411 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term102 _98584 _98585 s a f x b) (h2 : term104 _98584 _98585 s a f x b) : term102 _98584 _98585 s a f x b.
Proof. exact (@lem3791409 _98584 _98585 s a f x b h2 (@lem3791410 _98584 _98585 s a f x b h1)). Qed.
Lemma lem3791412 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term102 _98584 _98585 s a f x b) : term105 _98584 _98585 s a f x b.
Proof. exact (fun h0 : term104 _98584 _98585 s a f x b => @lem3791411 _98584 _98585 s a f x b h1 h0). Qed.
Lemma lem3791413 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term104 _98584 _98585 s a f x b) : term104 _98584 _98585 s a f x b.
Proof. exact (h1). Qed.
Lemma lem3791414 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term102 _98584 _98585 s a f x b) (h2 : term104 _98584 _98585 s a f x b) : term102 _98584 _98585 s a f x b.
Proof. exact (@lem3791412 _98584 _98585 s a f x b h1 (@lem3791413 _98584 _98585 s a f x b h2)). Qed.
Lemma lem3791415 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term104 _98584 _98585 s a f x b) : term104 _98584 _98585 s a f x b.
Proof. exact (fun h0 : term102 _98584 _98585 s a f x b => @lem3791414 _98584 _98585 s a f x b h0 h1). Qed.
Lemma lem3791416 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : term106 _98584 _98585 s a f x b.
Proof. exact (fun h0 : term104 _98584 _98585 s a f x b => @lem3791415 _98584 _98585 s a f x b h0). Qed.
Lemma lem3791419 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : term104 _98584 _98585 s a f x b.
Proof. exact (@lem3791416 _98584 _98585 s a f x b (@lem3791408 _98584 _98585 s a f x b)). Qed.
Lemma lem3791420 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : term104 _98584 _98585 s a f x b.
Proof. exact (@lem3791419 _98584 _98585 s a f x b). Qed.
Lemma lem3791442 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3791443 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term102 _98584 _98585 s a f x b) = (term107 _98584 _98585 s a f x b).
Proof. exact (@lem3791442 (term103 _98584 _98585 s a f x b)). Qed.
Lemma lem3791445 (t : Prop) : (term108 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3791446 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term107 _98584 _98585 s a f x b) = ((term86 _98584 _98585 s b a f x) = (term100 _98584 _98585 s a f x b)).
Proof. exact (@lem3791445 ((term86 _98584 _98585 s b a f x) = (term100 _98584 _98585 s a f x b))). Qed.
Lemma lem3791447 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term102 _98584 _98585 s a f x b) = ((term86 _98584 _98585 s b a f x) = (term100 _98584 _98585 s a f x b)).
Proof. exact (TRANS (@lem3791443 _98584 _98585 s a f x b) (@lem3791446 _98584 _98585 s a f x b)). Qed.
Lemma lem3791449 {A : Type'} (P : Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem3791450 {_98584 : Type'} (P : Prop) (Q : _98584 -> Prop) : (term109 _98584 P Q) = (term110 _98584 P Q).
Proof. exact (@lem3791449 _98584 P Q). Qed.
Lemma lem3791451 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term111 _98584 _98585 s b a f x) = (term112 _98584 _98585 s b a f x).
Proof. exact (@lem3791450 _98584 (s x) (term113 _98584 _98585 s b a f x)). Qed.
Lemma lem3791452 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term114 _98584 _98585 s b a f x c) = (term83 _98584 _98585 s b a f x c).
Proof. exact (eq_refl (term114 _98584 _98585 s b a f x c)). Qed.
Lemma lem3791453 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term69 _98585 s x) = (term69 _98585 s x).
Proof. exact (eq_refl (term69 _98585 s x)). Qed.
Lemma lem3791454 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term115 _98584 _98585 s b a f x c) = (term84 _98584 _98585 s b a f x c).
Proof. exact (MK_COMB (@lem3791453 _98585 s x) (@lem3791452 _98584 _98585 s b a f x c)). Qed.
Lemma lem3791455 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term116 _98584 _98585 s b a f x) = (term85 _98584 _98585 s b a f x).
Proof. exact (fun_ext (fun c : _98584 => @lem3791454 _98584 _98585 s b a f x c)). Qed.
Lemma lem3791456 {_98584 : Type'} : (@ex _98584) = (@ex _98584).
Proof. exact (eq_refl (@ex _98584)). Qed.
Lemma lem3791457 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term111 _98584 _98585 s b a f x) = (term86 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3791456 _98584) (@lem3791455 _98584 _98585 s b a f x)). Qed.
Lemma lem3791458 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3791459 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term117 _98584 _98585 s b a f x) = (term87 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3791458) (@lem3791457 _98584 _98585 s b a f x)). Qed.
Lemma lem3791460 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term114 _98584 _98585 s b a f x c) = (term83 _98584 _98585 s b a f x c).
Proof. exact (eq_refl (term114 _98584 _98585 s b a f x c)). Qed.
Lemma lem3791461 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term118 _98584 _98585 s b a f x) = (term113 _98584 _98585 s b a f x).
Proof. exact (fun_ext (fun c : _98584 => @lem3791460 _98584 _98585 s b a f x c)). Qed.
Lemma lem3791462 {_98584 : Type'} : (@ex _98584) = (@ex _98584).
Proof. exact (eq_refl (@ex _98584)). Qed.
Lemma lem3791463 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term119 _98584 _98585 s b a f x) = (term120 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3791462 _98584) (@lem3791461 _98584 _98585 s b a f x)). Qed.
Lemma lem3791464 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term69 _98585 s x) = (term69 _98585 s x).
Proof. exact (eq_refl (term69 _98585 s x)). Qed.
Lemma lem3791465 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term112 _98584 _98585 s b a f x) = (term121 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3791464 _98585 s x) (@lem3791463 _98584 _98585 s b a f x)). Qed.
Lemma lem3791466 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : ((term111 _98584 _98585 s b a f x) = (term112 _98584 _98585 s b a f x)) = ((term86 _98584 _98585 s b a f x) = (term121 _98584 _98585 s b a f x)).
Proof. exact (MK_COMB (@lem3791459 _98584 _98585 s b a f x) (@lem3791465 _98584 _98585 s b a f x)). Qed.
Lemma lem3791467 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term86 _98584 _98585 s b a f x) = (term121 _98584 _98585 s b a f x).
Proof. exact (EQ_MP (@lem3791466 _98584 _98585 s b a f x) (@lem3791451 _98584 _98585 s b a f x)). Qed.
Lemma lem3791528 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3791529 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term87 _98584 _98585 s b a f x) = (term122 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3791528) (@lem3791467 _98584 _98585 s b a f x)). Qed.
Lemma lem3791536 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term100 _98584 _98585 s a f x b) = (term100 _98584 _98585 s a f x b).
Proof. exact (eq_refl (term100 _98584 _98585 s a f x b)). Qed.
Lemma lem3791537 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : ((term86 _98584 _98585 s b a f x) = (term100 _98584 _98585 s a f x b)) = ((term121 _98584 _98585 s b a f x) = (term100 _98584 _98585 s a f x b)).
Proof. exact (MK_COMB (@lem3791529 _98584 _98585 s b a f x) (@lem3791536 _98584 _98585 s a f x b)). Qed.
Lemma lem3791538 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term102 _98584 _98585 s a f x b) = ((term121 _98584 _98585 s b a f x) = (term100 _98584 _98585 s a f x b)).
Proof. exact (TRANS (@lem3791447 _98584 _98585 s a f x b) (@lem3791537 _98584 _98585 s a f x b)). Qed.
Lemma lem3791539 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term123 _98584 _98585 a f x b) = (term124 _98584 _98585 a f x b).
Proof. exact (fun_ext (fun s : _98585 -> Prop => @lem3791538 _98584 _98585 s a f x b)). Qed.
Lemma lem3791540 {_98585 : Type'} : (@all (_98585 -> Prop)) = (@all (_98585 -> Prop)).
Proof. exact (eq_refl (@all (_98585 -> Prop))). Qed.
Lemma lem3791541 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term125 _98584 _98585 a f x b) = (term126 _98584 _98585 a f x b).
Proof. exact (MK_COMB (@lem3791540 _98585) (@lem3791539 _98584 _98585 a f x b)). Qed.
Lemma lem3791546 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term127 _98584 _98585 f x b) = (term128 _98584 _98585 f x b).
Proof. exact (fun_ext (fun a : _98584 => @lem3791541 _98584 _98585 a f x b)). Qed.
Lemma lem3791547 {_98584 : Type'} : (@all _98584) = (@all _98584).
Proof. exact (eq_refl (@all _98584)). Qed.
Lemma lem3791548 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term129 _98584 _98585 f x b) = (term130 _98584 _98585 f x b).
Proof. exact (MK_COMB (@lem3791547 _98584) (@lem3791546 _98584 _98585 f x b)). Qed.
Lemma lem3791553 {_98584 _98585 : Type'} (x : _98585) (b : _98584) : (term131 _98584 _98585 x b) = (term132 _98584 _98585 x b).
Proof. exact (fun_ext (fun f : type1467 _98584 _98585 => @lem3791548 _98584 _98585 f x b)). Qed.
Lemma lem3791554 {_98584 _98585 : Type'} : (@all (_98585 -> _98584 -> _98584)) = (@all (_98585 -> _98584 -> _98584)).
Proof. exact (eq_refl (@all (_98585 -> _98584 -> _98584))). Qed.
Lemma lem3791555 {_98584 _98585 : Type'} (x : _98585) (b : _98584) : (term133 _98584 _98585 x b) = (term134 _98584 _98585 x b).
Proof. exact (MK_COMB (@lem3791554 _98584 _98585) (@lem3791553 _98584 _98585 x b)). Qed.
Lemma lem3791560 {_98584 _98585 : Type'} (b : _98584) : (term135 _98584 _98585 b) = (term136 _98584 _98585 b).
Proof. exact (fun_ext (fun x : _98585 => @lem3791555 _98584 _98585 x b)). Qed.
Lemma lem3791561 {_98585 : Type'} : (@all _98585) = (@all _98585).
Proof. exact (eq_refl (@all _98585)). Qed.
Lemma lem3791562 {_98584 _98585 : Type'} (b : _98584) : (term137 _98584 _98585 b) = (term138 _98584 _98585 b).
Proof. exact (MK_COMB (@lem3791561 _98585) (@lem3791560 _98584 _98585 b)). Qed.
Lemma lem3791567 {_98584 _98585 : Type'} : (term139 _98584 _98585) = (term140 _98584 _98585).
Proof. exact (fun_ext (fun b : _98584 => @lem3791562 _98584 _98585 b)). Qed.
Lemma lem3791568 {_98584 : Type'} : (@all _98584) = (@all _98584).
Proof. exact (eq_refl (@all _98584)). Qed.
Lemma lem3791577 {_98584 _98585 : Type'} : (term141 _98584 _98585) = (term142 _98584 _98585).
Proof. exact (MK_COMB (@lem3791568 _98584) (@lem3791567 _98584 _98585)). Qed.
Lemma lem3791578 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (a = (f x b)) = (a = (f x b)).
Proof. exact (eq_refl (a = (f x b))). Qed.
Lemma lem3791583 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : ((s x') = (x' = x)) = ((s x') = (x' = x)).
Proof. exact (eq_refl ((s x') = (x' = x))). Qed.
Lemma lem3791584 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term97 _98585 s x) = (term97 _98585 s x).
Proof. exact (fun_ext (fun x' : _98585 => @lem3791583 _98585 s x' x)). Qed.
Lemma lem3791585 {_98585 : Type'} : (@all _98585) = (@all _98585).
Proof. exact (eq_refl (@all _98585)). Qed.
Lemma lem3791586 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term98 _98585 s x) = (term98 _98585 s x).
Proof. exact (MK_COMB (@lem3791585 _98585) (@lem3791584 _98585 s x)). Qed.
Lemma lem3791587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3791588 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term99 _98585 s x) = (term99 _98585 s x).
Proof. exact (MK_COMB (@lem3791587) (@lem3791586 _98585 s x)). Qed.
Lemma lem3791589 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term100 _98584 _98585 s a f x b) = (term100 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3791588 _98585 s x) (@lem3791578 _98584 _98585 a f x b)). Qed.
Lemma lem3791590 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (a = (f x c)) = (a = (f x c)).
Proof. exact (eq_refl (a = (f x c))). Qed.
Lemma lem3791591 {_98584 : Type'} (c : _98584) (b : _98584) : (c = b) = (c = b).
Proof. exact (eq_refl (c = b)). Qed.
Lemma lem3791600 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term76 _98585 s x' x) = (term76 _98585 s x' x).
Proof. exact (eq_refl (term76 _98585 s x' x)). Qed.
Lemma lem3791601 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term78 _98585 s x) = (term78 _98585 s x).
Proof. exact (fun_ext (fun x' : _98585 => @lem3791600 _98585 s x' x)). Qed.
Lemma lem3791602 {_98585 : Type'} : (@all _98585) = (@all _98585).
Proof. exact (eq_refl (@all _98585)). Qed.
Lemma lem3791603 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term79 _98585 s x) = (term79 _98585 s x).
Proof. exact (MK_COMB (@lem3791602 _98585) (@lem3791601 _98585 s x)). Qed.
Lemma lem3791604 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3791605 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term80 _98585 s x) = (term80 _98585 s x).
Proof. exact (MK_COMB (@lem3791604) (@lem3791603 _98585 s x)). Qed.
Lemma lem3791606 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term81 _98584 _98585 s x c b) = (term81 _98584 _98585 s x c b).
Proof. exact (MK_COMB (@lem3791605 _98585 s x) (@lem3791591 _98584 c b)). Qed.
Lemma lem3791607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3791608 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term82 _98584 _98585 s x c b) = (term82 _98584 _98585 s x c b).
Proof. exact (MK_COMB (@lem3791607) (@lem3791606 _98584 _98585 s x c b)). Qed.
Lemma lem3791609 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term83 _98584 _98585 s b a f x c) = (term83 _98584 _98585 s b a f x c).
Proof. exact (MK_COMB (@lem3791608 _98584 _98585 s x c b) (@lem3791590 _98584 _98585 a f x c)). Qed.
Lemma lem3791610 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term113 _98584 _98585 s b a f x) = (term113 _98584 _98585 s b a f x).
Proof. exact (fun_ext (fun c : _98584 => @lem3791609 _98584 _98585 s b a f x c)). Qed.
Lemma lem3791611 {_98584 : Type'} : (@ex _98584) = (@ex _98584).
Proof. exact (eq_refl (@ex _98584)). Qed.
Lemma lem3791612 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term120 _98584 _98585 s b a f x) = (term120 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3791611 _98584) (@lem3791610 _98584 _98585 s b a f x)). Qed.
Lemma lem3791615 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term69 _98585 s x) = (term69 _98585 s x).
Proof. exact (eq_refl (term69 _98585 s x)). Qed.
Lemma lem3791616 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term121 _98584 _98585 s b a f x) = (term121 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3791615 _98585 s x) (@lem3791612 _98584 _98585 s b a f x)). Qed.
Lemma lem3791617 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3791618 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term122 _98584 _98585 s b a f x) = (term122 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3791617) (@lem3791616 _98584 _98585 s b a f x)). Qed.
Lemma lem3791619 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : ((term121 _98584 _98585 s b a f x) = (term100 _98584 _98585 s a f x b)) = ((term121 _98584 _98585 s b a f x) = (term100 _98584 _98585 s a f x b)).
Proof. exact (MK_COMB (@lem3791618 _98584 _98585 s b a f x) (@lem3791589 _98584 _98585 s a f x b)). Qed.
Lemma lem3791620 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term124 _98584 _98585 a f x b) = (term124 _98584 _98585 a f x b).
Proof. exact (fun_ext (fun s : _98585 -> Prop => @lem3791619 _98584 _98585 s a f x b)). Qed.
Lemma lem3791621 {_98585 : Type'} : (@all (_98585 -> Prop)) = (@all (_98585 -> Prop)).
Proof. exact (eq_refl (@all (_98585 -> Prop))). Qed.
Lemma lem3791622 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term126 _98584 _98585 a f x b) = (term126 _98584 _98585 a f x b).
Proof. exact (MK_COMB (@lem3791621 _98585) (@lem3791620 _98584 _98585 a f x b)). Qed.
Lemma lem3791623 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term128 _98584 _98585 f x b) = (term128 _98584 _98585 f x b).
Proof. exact (fun_ext (fun a : _98584 => @lem3791622 _98584 _98585 a f x b)). Qed.
Lemma lem3791624 {_98584 : Type'} : (@all _98584) = (@all _98584).
Proof. exact (eq_refl (@all _98584)). Qed.
Lemma lem3791625 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term130 _98584 _98585 f x b) = (term130 _98584 _98585 f x b).
Proof. exact (MK_COMB (@lem3791624 _98584) (@lem3791623 _98584 _98585 f x b)). Qed.
Lemma lem3791626 {_98584 _98585 : Type'} (x : _98585) (b : _98584) : (term132 _98584 _98585 x b) = (term132 _98584 _98585 x b).
Proof. exact (fun_ext (fun f : type1467 _98584 _98585 => @lem3791625 _98584 _98585 f x b)). Qed.
Lemma lem3791627 {_98584 _98585 : Type'} : (@all (_98585 -> _98584 -> _98584)) = (@all (_98585 -> _98584 -> _98584)).
Proof. exact (eq_refl (@all (_98585 -> _98584 -> _98584))). Qed.
Lemma lem3791628 {_98584 _98585 : Type'} (x : _98585) (b : _98584) : (term134 _98584 _98585 x b) = (term134 _98584 _98585 x b).
Proof. exact (MK_COMB (@lem3791627 _98584 _98585) (@lem3791626 _98584 _98585 x b)). Qed.
Lemma lem3791629 {_98584 _98585 : Type'} (b : _98584) : (term136 _98584 _98585 b) = (term136 _98584 _98585 b).
Proof. exact (fun_ext (fun x : _98585 => @lem3791628 _98584 _98585 x b)). Qed.
Lemma lem3791630 {_98585 : Type'} : (@all _98585) = (@all _98585).
Proof. exact (eq_refl (@all _98585)). Qed.
Lemma lem3791631 {_98584 _98585 : Type'} (b : _98584) : (term138 _98584 _98585 b) = (term138 _98584 _98585 b).
Proof. exact (MK_COMB (@lem3791630 _98585) (@lem3791629 _98584 _98585 b)). Qed.
Lemma lem3791632 {_98584 _98585 : Type'} : (term140 _98584 _98585) = (term140 _98584 _98585).
Proof. exact (fun_ext (fun b : _98584 => @lem3791631 _98584 _98585 b)). Qed.
Lemma lem3791633 {_98584 : Type'} : (@all _98584) = (@all _98584).
Proof. exact (eq_refl (@all _98584)). Qed.
Lemma lem3791634 {_98584 _98585 : Type'} : (term142 _98584 _98585) = (term142 _98584 _98585).
Proof. exact (MK_COMB (@lem3791633 _98584) (@lem3791632 _98584 _98585)). Qed.
Lemma lem3791695 {_98584 _98585 : Type'} : (term141 _98584 _98585) = (term142 _98584 _98585).
Proof. exact (TRANS (@lem3791577 _98584 _98585) (@lem3791634 _98584 _98585)). Qed.
Lemma lem3791696 {_98584 _98585 : Type'} : (term142 _98584 _98585) = (term141 _98584 _98585).
Proof. exact (SYM (@lem3791695 _98584 _98585)). Qed.
Lemma lem3791698 (p : Prop) : p = (term101 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3791699 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : ((term121 _98584 _98585 s b a f x) = (term100 _98584 _98585 s a f x b)) = (term143 _98584 _98585 s a f x b).
Proof. exact (@lem3791698 ((term121 _98584 _98585 s b a f x) = (term100 _98584 _98585 s a f x b))). Qed.
Lemma lem3791700 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term143 _98584 _98585 s a f x b) = ((term121 _98584 _98585 s b a f x) = (term100 _98584 _98585 s a f x b)).
Proof. exact (SYM (@lem3791699 _98584 _98585 s a f x b)). Qed.
Lemma lem3791701 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term144 _98584 _98585 s a f x b) : term144 _98584 _98585 s a f x b.
Proof. exact (h1). Qed.
Lemma lem3791709 {_98585 : Type'} (x' : _98585) (x : _98585) : (term145 _98585 x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3791711 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) : (term146 _98585 s x') = (term146 _98585 s x').
Proof. exact (eq_refl (term146 _98585 s x')). Qed.
Lemma lem3791712 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term147 _98585 s x' x) = (term148 _98585 s x' x).
Proof. exact (MK_COMB (@lem3791711 _98585 s x') (@lem3791709 _98585 x' x)). Qed.
Lemma lem3791713 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term76 _98585 s x' x) = (term147 _98585 s x' x).
Proof. exact (@lem17045 (s x') (term72 _98585 x' x)). Qed.
Lemma lem3791714 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term76 _98585 s x' x) = (term148 _98585 s x' x).
Proof. exact (TRANS (@lem3791713 _98585 s x' x) (@lem3791712 _98585 s x' x)). Qed.
Lemma lem3791719 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term149 _98585 s x' x) = (term73 _98585 s x' x).
Proof. exact (@lem16933 (term73 _98585 s x' x)). Qed.
Lemma lem3791720 {_98585 : Type'} (P : _98585 -> Prop) : (term150 _98585 P) = (term151 _98585 P).
Proof. exact (@lem18392 _98585 P). Qed.
Lemma lem3791721 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term152 _98585 s x) = (term153 _98585 s x).
Proof. exact (@lem3791720 _98585 (term78 _98585 s x)). Qed.
Lemma lem3791722 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term154 _98585 s x x') = (term76 _98585 s x' x).
Proof. exact (eq_refl (term154 _98585 s x x')). Qed.
Lemma lem3791723 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3791724 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term155 _98585 s x x') = (term149 _98585 s x' x).
Proof. exact (MK_COMB (@lem3791723) (@lem3791722 _98585 s x' x)). Qed.
Lemma lem3791725 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term155 _98585 s x x') = (term73 _98585 s x' x).
Proof. exact (TRANS (@lem3791724 _98585 s x' x) (@lem3791719 _98585 s x' x)). Qed.
Lemma lem3791726 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term156 _98585 s x) = (term157 _98585 s x).
Proof. exact (fun_ext (fun x' : _98585 => @lem3791725 _98585 s x' x)). Qed.
Lemma lem3791727 {_98585 : Type'} : (@ex _98585) = (@ex _98585).
Proof. exact (eq_refl (@ex _98585)). Qed.
Lemma lem3791728 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term153 _98585 s x) = (term158 _98585 s x).
Proof. exact (MK_COMB (@lem3791727 _98585) (@lem3791726 _98585 s x)). Qed.
Lemma lem3791729 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term152 _98585 s x) = (term158 _98585 s x).
Proof. exact (TRANS (@lem3791721 _98585 s x) (@lem3791728 _98585 s x)). Qed.
Lemma lem3791730 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term78 _98585 s x) = (term159 _98585 s x).
Proof. exact (fun_ext (fun x' : _98585 => @lem3791714 _98585 s x' x)). Qed.
Lemma lem3791731 {_98585 : Type'} : (@all _98585) = (@all _98585).
Proof. exact (eq_refl (@all _98585)). Qed.
Lemma lem3791732 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term79 _98585 s x) = (term160 _98585 s x).
Proof. exact (MK_COMB (@lem3791731 _98585) (@lem3791730 _98585 s x)). Qed.
Lemma lem3791733 {_98584 : Type'} (c : _98584) (b : _98584) : (term72 _98584 c b) = (term72 _98584 c b).
Proof. exact (eq_refl (term72 _98584 c b)). Qed.
Lemma lem3791734 {_98584 : Type'} (c : _98584) (b : _98584) : (c = b) = (c = b).
Proof. exact (eq_refl (c = b)). Qed.
Lemma lem3791735 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3791736 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term161 _98585 s x) = (term162 _98585 s x).
Proof. exact (MK_COMB (@lem3791735) (@lem3791729 _98585 s x)). Qed.
Lemma lem3791737 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term163 _98584 _98585 s x c b) = (term164 _98584 _98585 s x c b).
Proof. exact (MK_COMB (@lem3791736 _98585 s x) (@lem3791733 _98584 c b)). Qed.
Lemma lem3791738 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term165 _98584 _98585 s x c b) = (term163 _98584 _98585 s x c b).
Proof. exact (@lem17045 (term79 _98585 s x) (c = b)). Qed.
Lemma lem3791739 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term165 _98584 _98585 s x c b) = (term164 _98584 _98585 s x c b).
Proof. exact (TRANS (@lem3791738 _98584 _98585 s x c b) (@lem3791737 _98584 _98585 s x c b)). Qed.
Lemma lem3791740 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3791741 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term80 _98585 s x) = (term166 _98585 s x).
Proof. exact (MK_COMB (@lem3791740) (@lem3791732 _98585 s x)). Qed.
Lemma lem3791742 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term81 _98584 _98585 s x c b) = (term167 _98584 _98585 s x c b).
Proof. exact (MK_COMB (@lem3791741 _98585 s x) (@lem3791734 _98584 c b)). Qed.
Lemma lem3791743 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term168 _98584 _98585 a f x c) = (term168 _98584 _98585 a f x c).
Proof. exact (eq_refl (term168 _98584 _98585 a f x c)). Qed.
Lemma lem3791744 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (a = (f x c)) = (a = (f x c)).
Proof. exact (eq_refl (a = (f x c))). Qed.
Lemma lem3791745 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3791746 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term169 _98584 _98585 s x c b) = (term170 _98584 _98585 s x c b).
Proof. exact (MK_COMB (@lem3791745) (@lem3791739 _98584 _98585 s x c b)). Qed.
Lemma lem3791747 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term171 _98584 _98585 s b a f x c) = (term172 _98584 _98585 s b a f x c).
Proof. exact (MK_COMB (@lem3791746 _98584 _98585 s x c b) (@lem3791743 _98584 _98585 a f x c)). Qed.
Lemma lem3791748 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term173 _98584 _98585 s b a f x c) = (term171 _98584 _98585 s b a f x c).
Proof. exact (@lem17045 (term81 _98584 _98585 s x c b) (a = (f x c))). Qed.
Lemma lem3791749 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term173 _98584 _98585 s b a f x c) = (term172 _98584 _98585 s b a f x c).
Proof. exact (TRANS (@lem3791748 _98584 _98585 s b a f x c) (@lem3791747 _98584 _98585 s b a f x c)). Qed.
Lemma lem3791750 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3791751 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term82 _98584 _98585 s x c b) = (term174 _98584 _98585 s x c b).
Proof. exact (MK_COMB (@lem3791750) (@lem3791742 _98584 _98585 s x c b)). Qed.
Lemma lem3791752 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term83 _98584 _98585 s b a f x c) = (term175 _98584 _98585 s b a f x c).
Proof. exact (MK_COMB (@lem3791751 _98584 _98585 s x c b) (@lem3791744 _98584 _98585 a f x c)). Qed.
Lemma lem3791753 {_98584 : Type'} (P : _98584 -> Prop) : (term176 _98584 P) = (term177 _98584 P).
Proof. exact (@lem18394 _98584 P). Qed.
Lemma lem3791754 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term178 _98584 _98585 s b a f x) = (term179 _98584 _98585 s b a f x).
Proof. exact (@lem3791753 _98584 (term113 _98584 _98585 s b a f x)). Qed.
Lemma lem3791755 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term114 _98584 _98585 s b a f x c) = (term83 _98584 _98585 s b a f x c).
Proof. exact (eq_refl (term114 _98584 _98585 s b a f x c)). Qed.
Lemma lem3791756 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3791757 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term180 _98584 _98585 s b a f x c) = (term173 _98584 _98585 s b a f x c).
Proof. exact (MK_COMB (@lem3791756) (@lem3791755 _98584 _98585 s b a f x c)). Qed.
Lemma lem3791758 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term180 _98584 _98585 s b a f x c) = (term172 _98584 _98585 s b a f x c).
Proof. exact (TRANS (@lem3791757 _98584 _98585 s b a f x c) (@lem3791749 _98584 _98585 s b a f x c)). Qed.
Lemma lem3791759 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term181 _98584 _98585 s b a f x) = (term182 _98584 _98585 s b a f x).
Proof. exact (fun_ext (fun c : _98584 => @lem3791758 _98584 _98585 s b a f x c)). Qed.
Lemma lem3791760 {_98584 : Type'} : (@all _98584) = (@all _98584).
Proof. exact (eq_refl (@all _98584)). Qed.
Lemma lem3791761 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term179 _98584 _98585 s b a f x) = (term183 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3791760 _98584) (@lem3791759 _98584 _98585 s b a f x)). Qed.
Lemma lem3791762 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term178 _98584 _98585 s b a f x) = (term183 _98584 _98585 s b a f x).
Proof. exact (TRANS (@lem3791754 _98584 _98585 s b a f x) (@lem3791761 _98584 _98585 s b a f x)). Qed.
Lemma lem3791763 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term113 _98584 _98585 s b a f x) = (term184 _98584 _98585 s b a f x).
Proof. exact (fun_ext (fun c : _98584 => @lem3791752 _98584 _98585 s b a f x c)). Qed.
Lemma lem3791764 {_98584 : Type'} : (@ex _98584) = (@ex _98584).
Proof. exact (eq_refl (@ex _98584)). Qed.
Lemma lem3791765 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term120 _98584 _98585 s b a f x) = (term185 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3791764 _98584) (@lem3791763 _98584 _98585 s b a f x)). Qed.
Lemma lem3791767 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term146 _98585 s x) = (term146 _98585 s x).
Proof. exact (eq_refl (term146 _98585 s x)). Qed.
Lemma lem3791768 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term186 _98584 _98585 s b a f x) = (term187 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3791767 _98585 s x) (@lem3791762 _98584 _98585 s b a f x)). Qed.
Lemma lem3791769 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term188 _98584 _98585 s b a f x) = (term186 _98584 _98585 s b a f x).
Proof. exact (@lem17045 (s x) (term120 _98584 _98585 s b a f x)). Qed.
Lemma lem3791770 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term188 _98584 _98585 s b a f x) = (term187 _98584 _98585 s b a f x).
Proof. exact (TRANS (@lem3791769 _98584 _98585 s b a f x) (@lem3791768 _98584 _98585 s b a f x)). Qed.
Lemma lem3791772 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term69 _98585 s x) = (term69 _98585 s x).
Proof. exact (eq_refl (term69 _98585 s x)). Qed.
Lemma lem3791773 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term121 _98584 _98585 s b a f x) = (term189 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3791772 _98585 s x) (@lem3791765 _98584 _98585 s b a f x)). Qed.
Lemma lem3791788 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term190 _98585 s x' x) = (term191 _98585 s x' x).
Proof. exact (@lem17930 (s x') (x' = x)). Qed.
Lemma lem3791799 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : ((s x') = (x' = x)) = (term192 _98585 s x' x).
Proof. exact (@lem17784 (s x') (x' = x)). Qed.
Lemma lem3791800 {_98585 : Type'} (P : _98585 -> Prop) : (term150 _98585 P) = (term151 _98585 P).
Proof. exact (@lem18392 _98585 P). Qed.
Lemma lem3791801 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term193 _98585 s x) = (term194 _98585 s x).
Proof. exact (@lem3791800 _98585 (term97 _98585 s x)). Qed.
Lemma lem3791802 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term195 _98585 s x x') = ((s x') = (x' = x)).
Proof. exact (eq_refl (term195 _98585 s x x')). Qed.
Lemma lem3791803 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3791804 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term196 _98585 s x x') = (term190 _98585 s x' x).
Proof. exact (MK_COMB (@lem3791803) (@lem3791802 _98585 s x' x)). Qed.
Lemma lem3791805 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term196 _98585 s x x') = (term191 _98585 s x' x).
Proof. exact (TRANS (@lem3791804 _98585 s x' x) (@lem3791788 _98585 s x' x)). Qed.
Lemma lem3791806 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term197 _98585 s x) = (term198 _98585 s x).
Proof. exact (fun_ext (fun x' : _98585 => @lem3791805 _98585 s x' x)). Qed.
Lemma lem3791807 {_98585 : Type'} : (@ex _98585) = (@ex _98585).
Proof. exact (eq_refl (@ex _98585)). Qed.
Lemma lem3791808 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term194 _98585 s x) = (term199 _98585 s x).
Proof. exact (MK_COMB (@lem3791807 _98585) (@lem3791806 _98585 s x)). Qed.
Lemma lem3791809 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term193 _98585 s x) = (term199 _98585 s x).
Proof. exact (TRANS (@lem3791801 _98585 s x) (@lem3791808 _98585 s x)). Qed.
Lemma lem3791810 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term97 _98585 s x) = (term200 _98585 s x).
Proof. exact (fun_ext (fun x' : _98585 => @lem3791799 _98585 s x' x)). Qed.
Lemma lem3791811 {_98585 : Type'} : (@all _98585) = (@all _98585).
Proof. exact (eq_refl (@all _98585)). Qed.
Lemma lem3791812 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term98 _98585 s x) = (term201 _98585 s x).
Proof. exact (MK_COMB (@lem3791811 _98585) (@lem3791810 _98585 s x)). Qed.
Lemma lem3791813 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term168 _98584 _98585 a f x b) = (term168 _98584 _98585 a f x b).
Proof. exact (eq_refl (term168 _98584 _98585 a f x b)). Qed.
Lemma lem3791814 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (a = (f x b)) = (a = (f x b)).
Proof. exact (eq_refl (a = (f x b))). Qed.
Lemma lem3791815 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3791816 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term202 _98585 s x) = (term203 _98585 s x).
Proof. exact (MK_COMB (@lem3791815) (@lem3791809 _98585 s x)). Qed.
Lemma lem3791817 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term204 _98584 _98585 s a f x b) = (term205 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3791816 _98585 s x) (@lem3791813 _98584 _98585 a f x b)). Qed.
Lemma lem3791818 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term206 _98584 _98585 s a f x b) = (term204 _98584 _98585 s a f x b).
Proof. exact (@lem17045 (term98 _98585 s x) (a = (f x b))). Qed.
Lemma lem3791819 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term206 _98584 _98585 s a f x b) = (term205 _98584 _98585 s a f x b).
Proof. exact (TRANS (@lem3791818 _98584 _98585 s a f x b) (@lem3791817 _98584 _98585 s a f x b)). Qed.
Lemma lem3791820 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3791821 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term99 _98585 s x) = (term207 _98585 s x).
Proof. exact (MK_COMB (@lem3791820) (@lem3791812 _98585 s x)). Qed.
Lemma lem3791822 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term100 _98584 _98585 s a f x b) = (term208 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3791821 _98585 s x) (@lem3791814 _98584 _98585 a f x b)). Qed.
Lemma lem3791823 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3791824 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term209 _98584 _98585 s b a f x) = (term210 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3791823) (@lem3791770 _98584 _98585 s b a f x)). Qed.
Lemma lem3791825 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term211 _98584 _98585 s a f x b) = (term212 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3791824 _98584 _98585 s b a f x) (@lem3791822 _98584 _98585 s a f x b)). Qed.
Lemma lem3791826 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3791827 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term213 _98584 _98585 s b a f x) = (term214 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3791826) (@lem3791773 _98584 _98585 s b a f x)). Qed.
Lemma lem3791828 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term215 _98584 _98585 s a f x b) = (term216 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3791827 _98584 _98585 s b a f x) (@lem3791819 _98584 _98585 s a f x b)). Qed.
Lemma lem3791829 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3791830 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term217 _98584 _98585 s a f x b) = (term218 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3791829) (@lem3791828 _98584 _98585 s a f x b)). Qed.
Lemma lem3791831 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term219 _98584 _98585 s a f x b) = (term220 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3791830 _98584 _98585 s a f x b) (@lem3791825 _98584 _98585 s a f x b)). Qed.
Lemma lem3791832 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term144 _98584 _98585 s a f x b) = (term219 _98584 _98585 s a f x b).
Proof. exact (@lem17646 (term121 _98584 _98585 s b a f x) (term100 _98584 _98585 s a f x b)). Qed.
Lemma lem3791833 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term144 _98584 _98585 s a f x b) = (term220 _98584 _98585 s a f x b).
Proof. exact (TRANS (@lem3791832 _98584 _98585 s a f x b) (@lem3791831 _98584 _98585 s a f x b)). Qed.
Lemma lem3792055 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3792056 {_98585 : Type'} (P : _98585 -> Prop) (Q : _98585 -> Prop) : (term221 _98585 P Q) = (term222 _98585 P Q).
Proof. exact (@lem3792055 _98585 P Q). Qed.
Lemma lem3792057 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term223 _98585 s x) = (term224 _98585 s x).
Proof. exact (@lem3792056 _98585 (term225 _98585 s x) (term159 _98585 s x)). Qed.
Lemma lem3792058 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term226 _98585 s x x') = (term227 _98585 s x' x).
Proof. exact (eq_refl (term226 _98585 s x x')). Qed.
Lemma lem3792059 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3792060 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term228 _98585 s x x') = (term229 _98585 s x' x).
Proof. exact (MK_COMB (@lem3792059) (@lem3792058 _98585 s x' x)). Qed.
Lemma lem3792061 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term230 _98585 s x x') = (term148 _98585 s x' x).
Proof. exact (eq_refl (term230 _98585 s x x')). Qed.
Lemma lem3792062 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term231 _98585 s x x') = (term192 _98585 s x' x).
Proof. exact (MK_COMB (@lem3792060 _98585 s x' x) (@lem3792061 _98585 s x' x)). Qed.
Lemma lem3792063 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term232 _98585 s x) = (term200 _98585 s x).
Proof. exact (fun_ext (fun x' : _98585 => @lem3792062 _98585 s x' x)). Qed.
Lemma lem3792064 {_98585 : Type'} : (@all _98585) = (@all _98585).
Proof. exact (eq_refl (@all _98585)). Qed.
Lemma lem3792065 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term223 _98585 s x) = (term201 _98585 s x).
Proof. exact (MK_COMB (@lem3792064 _98585) (@lem3792063 _98585 s x)). Qed.
Lemma lem3792066 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3792067 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term233 _98585 s x) = (term234 _98585 s x).
Proof. exact (MK_COMB (@lem3792066) (@lem3792065 _98585 s x)). Qed.
Lemma lem3792068 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term226 _98585 s x x') = (term227 _98585 s x' x).
Proof. exact (eq_refl (term226 _98585 s x x')). Qed.
Lemma lem3792069 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term235 _98585 s x) = (term225 _98585 s x).
Proof. exact (fun_ext (fun x' : _98585 => @lem3792068 _98585 s x' x)). Qed.
Lemma lem3792070 {_98585 : Type'} : (@all _98585) = (@all _98585).
Proof. exact (eq_refl (@all _98585)). Qed.
Lemma lem3792071 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term236 _98585 s x) = (term237 _98585 s x).
Proof. exact (MK_COMB (@lem3792070 _98585) (@lem3792069 _98585 s x)). Qed.
Lemma lem3792072 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3792073 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term238 _98585 s x) = (term239 _98585 s x).
Proof. exact (MK_COMB (@lem3792072) (@lem3792071 _98585 s x)). Qed.
Lemma lem3792074 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term230 _98585 s x x') = (term148 _98585 s x' x).
Proof. exact (eq_refl (term230 _98585 s x x')). Qed.
Lemma lem3792075 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term240 _98585 s x) = (term159 _98585 s x).
Proof. exact (fun_ext (fun x' : _98585 => @lem3792074 _98585 s x' x)). Qed.
Lemma lem3792076 {_98585 : Type'} : (@all _98585) = (@all _98585).
Proof. exact (eq_refl (@all _98585)). Qed.
Lemma lem3792077 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term241 _98585 s x) = (term160 _98585 s x).
Proof. exact (MK_COMB (@lem3792076 _98585) (@lem3792075 _98585 s x)). Qed.
Lemma lem3792078 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term224 _98585 s x) = (term242 _98585 s x).
Proof. exact (MK_COMB (@lem3792073 _98585 s x) (@lem3792077 _98585 s x)). Qed.
Lemma lem3792079 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : ((term223 _98585 s x) = (term224 _98585 s x)) = ((term201 _98585 s x) = (term242 _98585 s x)).
Proof. exact (MK_COMB (@lem3792067 _98585 s x) (@lem3792078 _98585 s x)). Qed.
Lemma lem3792080 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term201 _98585 s x) = (term242 _98585 s x).
Proof. exact (EQ_MP (@lem3792079 _98585 s x) (@lem3792057 _98585 s x)). Qed.
Lemma lem3792157 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3792158 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term207 _98585 s x) = (term243 _98585 s x).
Proof. exact (MK_COMB (@lem3792157) (@lem3792080 _98585 s x)). Qed.
Lemma lem3792159 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (a = (f x b)) = (a = (f x b)).
Proof. exact (eq_refl (a = (f x b))). Qed.
Lemma lem3792160 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term208 _98584 _98585 s a f x b) = (term244 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792158 _98585 s x) (@lem3792159 _98584 _98585 a f x b)). Qed.
Lemma lem3792161 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term210 _98584 _98585 s b a f x) = (term210 _98584 _98585 s b a f x).
Proof. exact (eq_refl (term210 _98584 _98585 s b a f x)). Qed.
Lemma lem3792162 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term212 _98584 _98585 s a f x b) = (term245 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792161 _98584 _98585 s b a f x) (@lem3792160 _98584 _98585 s a f x b)). Qed.
Lemma lem3792163 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term218 _98584 _98585 s a f x b) = (term218 _98584 _98585 s a f x b).
Proof. exact (eq_refl (term218 _98584 _98585 s a f x b)). Qed.
Lemma lem3792164 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term220 _98584 _98585 s a f x b) = (term246 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792163 _98584 _98585 s a f x b) (@lem3792162 _98584 _98585 s a f x b)). Qed.
Lemma lem3792166 {A : Type'} (P : Prop) (Q : A -> Prop) : (term110 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3792167 {_98584 : Type'} (P : Prop) (Q : _98584 -> Prop) : (term110 _98584 P Q) = (term109 _98584 P Q).
Proof. exact (@lem3792166 _98584 P Q). Qed.
Lemma lem3792168 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term247 _98584 _98585 s b a f x) = (term248 _98584 _98585 s b a f x).
Proof. exact (@lem3792167 _98584 (s x) (term184 _98584 _98585 s b a f x)). Qed.
Lemma lem3792169 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term249 _98584 _98585 s b a f x c) = (term175 _98584 _98585 s b a f x c).
Proof. exact (eq_refl (term249 _98584 _98585 s b a f x c)). Qed.
Lemma lem3792170 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term250 _98584 _98585 s b a f x) = (term184 _98584 _98585 s b a f x).
Proof. exact (fun_ext (fun c : _98584 => @lem3792169 _98584 _98585 s b a f x c)). Qed.
Lemma lem3792171 {_98584 : Type'} : (@ex _98584) = (@ex _98584).
Proof. exact (eq_refl (@ex _98584)). Qed.
Lemma lem3792172 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term251 _98584 _98585 s b a f x) = (term185 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3792171 _98584) (@lem3792170 _98584 _98585 s b a f x)). Qed.
Lemma lem3792173 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term69 _98585 s x) = (term69 _98585 s x).
Proof. exact (eq_refl (term69 _98585 s x)). Qed.
Lemma lem3792174 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term247 _98584 _98585 s b a f x) = (term189 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3792173 _98585 s x) (@lem3792172 _98584 _98585 s b a f x)). Qed.
Lemma lem3792175 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3792176 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term252 _98584 _98585 s b a f x) = (term253 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3792175) (@lem3792174 _98584 _98585 s b a f x)). Qed.
Lemma lem3792177 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term249 _98584 _98585 s b a f x c) = (term175 _98584 _98585 s b a f x c).
Proof. exact (eq_refl (term249 _98584 _98585 s b a f x c)). Qed.
Lemma lem3792178 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term69 _98585 s x) = (term69 _98585 s x).
Proof. exact (eq_refl (term69 _98585 s x)). Qed.
Lemma lem3792179 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term254 _98584 _98585 s b a f x c) = (term255 _98584 _98585 s b a f x c).
Proof. exact (MK_COMB (@lem3792178 _98585 s x) (@lem3792177 _98584 _98585 s b a f x c)). Qed.
Lemma lem3792180 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term256 _98584 _98585 s b a f x) = (term257 _98584 _98585 s b a f x).
Proof. exact (fun_ext (fun c : _98584 => @lem3792179 _98584 _98585 s b a f x c)). Qed.
Lemma lem3792181 {_98584 : Type'} : (@ex _98584) = (@ex _98584).
Proof. exact (eq_refl (@ex _98584)). Qed.
Lemma lem3792182 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term248 _98584 _98585 s b a f x) = (term258 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3792181 _98584) (@lem3792180 _98584 _98585 s b a f x)). Qed.
Lemma lem3792183 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : ((term247 _98584 _98585 s b a f x) = (term248 _98584 _98585 s b a f x)) = ((term189 _98584 _98585 s b a f x) = (term258 _98584 _98585 s b a f x)).
Proof. exact (MK_COMB (@lem3792176 _98584 _98585 s b a f x) (@lem3792182 _98584 _98585 s b a f x)). Qed.
Lemma lem3792184 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term189 _98584 _98585 s b a f x) = (term258 _98584 _98585 s b a f x).
Proof. exact (EQ_MP (@lem3792183 _98584 _98585 s b a f x) (@lem3792168 _98584 _98585 s b a f x)). Qed.
Lemma lem3792185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3792186 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term214 _98584 _98585 s b a f x) = (term259 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3792185) (@lem3792184 _98584 _98585 s b a f x)). Qed.
Lemma lem3792188 {A : Type'} (P : A -> Prop) (Q : Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3792189 {_98585 : Type'} (P : _98585 -> Prop) (Q : Prop) : (term260 _98585 P Q) = (term261 _98585 P Q).
Proof. exact (@lem3792188 _98585 P Q). Qed.
Lemma lem3792190 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term262 _98584 _98585 s a f x b) = (term263 _98584 _98585 s a f x b).
Proof. exact (@lem3792189 _98585 (term198 _98585 s x) (term168 _98584 _98585 a f x b)). Qed.
Lemma lem3792191 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term264 _98585 s x x') = (term191 _98585 s x' x).
Proof. exact (eq_refl (term264 _98585 s x x')). Qed.
Lemma lem3792192 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term265 _98585 s x) = (term198 _98585 s x).
Proof. exact (fun_ext (fun x' : _98585 => @lem3792191 _98585 s x' x)). Qed.
Lemma lem3792193 {_98585 : Type'} : (@ex _98585) = (@ex _98585).
Proof. exact (eq_refl (@ex _98585)). Qed.
Lemma lem3792194 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term266 _98585 s x) = (term199 _98585 s x).
Proof. exact (MK_COMB (@lem3792193 _98585) (@lem3792192 _98585 s x)). Qed.
Lemma lem3792195 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3792196 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term267 _98585 s x) = (term203 _98585 s x).
Proof. exact (MK_COMB (@lem3792195) (@lem3792194 _98585 s x)). Qed.
Lemma lem3792197 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term168 _98584 _98585 a f x b) = (term168 _98584 _98585 a f x b).
Proof. exact (eq_refl (term168 _98584 _98585 a f x b)). Qed.
Lemma lem3792198 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term262 _98584 _98585 s a f x b) = (term205 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792196 _98585 s x) (@lem3792197 _98584 _98585 a f x b)). Qed.
Lemma lem3792199 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3792200 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term268 _98584 _98585 s a f x b) = (term269 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792199) (@lem3792198 _98584 _98585 s a f x b)). Qed.
Lemma lem3792201 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term264 _98585 s x x') = (term191 _98585 s x' x).
Proof. exact (eq_refl (term264 _98585 s x x')). Qed.
Lemma lem3792202 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3792203 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term270 _98585 s x x') = (term271 _98585 s x' x).
Proof. exact (MK_COMB (@lem3792202) (@lem3792201 _98585 s x' x)). Qed.
Lemma lem3792204 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term168 _98584 _98585 a f x b) = (term168 _98584 _98585 a f x b).
Proof. exact (eq_refl (term168 _98584 _98585 a f x b)). Qed.
Lemma lem3792205 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term272 _98584 _98585 s x' a f x b) = (term273 _98584 _98585 s x' a f x b).
Proof. exact (MK_COMB (@lem3792203 _98585 s x' x) (@lem3792204 _98584 _98585 a f x b)). Qed.
Lemma lem3792206 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term274 _98584 _98585 s a f x b) = (term275 _98584 _98585 s a f x b).
Proof. exact (fun_ext (fun x' : _98585 => @lem3792205 _98584 _98585 s x' a f x b)). Qed.
Lemma lem3792207 {_98585 : Type'} : (@ex _98585) = (@ex _98585).
Proof. exact (eq_refl (@ex _98585)). Qed.
Lemma lem3792208 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term263 _98584 _98585 s a f x b) = (term276 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792207 _98585) (@lem3792206 _98584 _98585 s a f x b)). Qed.
Lemma lem3792209 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : ((term262 _98584 _98585 s a f x b) = (term263 _98584 _98585 s a f x b)) = ((term205 _98584 _98585 s a f x b) = (term276 _98584 _98585 s a f x b)).
Proof. exact (MK_COMB (@lem3792200 _98584 _98585 s a f x b) (@lem3792208 _98584 _98585 s a f x b)). Qed.
Lemma lem3792210 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term205 _98584 _98585 s a f x b) = (term276 _98584 _98585 s a f x b).
Proof. exact (EQ_MP (@lem3792209 _98584 _98585 s a f x b) (@lem3792190 _98584 _98585 s a f x b)). Qed.
Lemma lem3792211 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term216 _98584 _98585 s a f x b) = (term277 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792186 _98584 _98585 s b a f x) (@lem3792210 _98584 _98585 s a f x b)). Qed.
Lemma lem3792213 {A : Type'} (P : A -> Prop) (Q : Prop) : (term278 A P Q) = (term279 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3792214 {_98584 : Type'} (P : _98584 -> Prop) (Q : Prop) : (term278 _98584 P Q) = (term279 _98584 P Q).
Proof. exact (@lem3792213 _98584 P Q). Qed.
Lemma lem3792215 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term280 _98584 _98585 s a f x b) = (term281 _98584 _98585 s a f x b).
Proof. exact (@lem3792214 _98584 (term257 _98584 _98585 s b a f x) (term276 _98584 _98585 s a f x b)). Qed.
Lemma lem3792216 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term282 _98584 _98585 s b a f x c) = (term255 _98584 _98585 s b a f x c).
Proof. exact (eq_refl (term282 _98584 _98585 s b a f x c)). Qed.
Lemma lem3792217 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term283 _98584 _98585 s b a f x) = (term257 _98584 _98585 s b a f x).
Proof. exact (fun_ext (fun c : _98584 => @lem3792216 _98584 _98585 s b a f x c)). Qed.
Lemma lem3792218 {_98584 : Type'} : (@ex _98584) = (@ex _98584).
Proof. exact (eq_refl (@ex _98584)). Qed.
Lemma lem3792219 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term284 _98584 _98585 s b a f x) = (term258 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3792218 _98584) (@lem3792217 _98584 _98585 s b a f x)). Qed.
Lemma lem3792220 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3792221 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term285 _98584 _98585 s b a f x) = (term259 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3792220) (@lem3792219 _98584 _98585 s b a f x)). Qed.
Lemma lem3792222 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term276 _98584 _98585 s a f x b) = (term276 _98584 _98585 s a f x b).
Proof. exact (eq_refl (term276 _98584 _98585 s a f x b)). Qed.
Lemma lem3792223 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term280 _98584 _98585 s a f x b) = (term277 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792221 _98584 _98585 s b a f x) (@lem3792222 _98584 _98585 s a f x b)). Qed.
Lemma lem3792224 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3792225 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term286 _98584 _98585 s a f x b) = (term287 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792224) (@lem3792223 _98584 _98585 s a f x b)). Qed.
Lemma lem3792226 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term282 _98584 _98585 s b a f x c) = (term255 _98584 _98585 s b a f x c).
Proof. exact (eq_refl (term282 _98584 _98585 s b a f x c)). Qed.
Lemma lem3792227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3792228 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term288 _98584 _98585 s b a f x c) = (term289 _98584 _98585 s b a f x c).
Proof. exact (MK_COMB (@lem3792227) (@lem3792226 _98584 _98585 s b a f x c)). Qed.
Lemma lem3792229 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term276 _98584 _98585 s a f x b) = (term276 _98584 _98585 s a f x b).
Proof. exact (eq_refl (term276 _98584 _98585 s a f x b)). Qed.
Lemma lem3792230 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term290 _98584 _98585 c s a f x b) = (term291 _98584 _98585 c s a f x b).
Proof. exact (MK_COMB (@lem3792228 _98584 _98585 s b a f x c) (@lem3792229 _98584 _98585 s a f x b)). Qed.
Lemma lem3792231 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term292 _98584 _98585 s a f x b) = (term293 _98584 _98585 s a f x b).
Proof. exact (fun_ext (fun c : _98584 => @lem3792230 _98584 _98585 c s a f x b)). Qed.
Lemma lem3792232 {_98584 : Type'} : (@ex _98584) = (@ex _98584).
Proof. exact (eq_refl (@ex _98584)). Qed.
Lemma lem3792233 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term281 _98584 _98585 s a f x b) = (term294 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792232 _98584) (@lem3792231 _98584 _98585 s a f x b)). Qed.
Lemma lem3792234 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : ((term280 _98584 _98585 s a f x b) = (term281 _98584 _98585 s a f x b)) = ((term277 _98584 _98585 s a f x b) = (term294 _98584 _98585 s a f x b)).
Proof. exact (MK_COMB (@lem3792225 _98584 _98585 s a f x b) (@lem3792233 _98584 _98585 s a f x b)). Qed.
Lemma lem3792235 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term277 _98584 _98585 s a f x b) = (term294 _98584 _98585 s a f x b).
Proof. exact (EQ_MP (@lem3792234 _98584 _98585 s a f x b) (@lem3792215 _98584 _98585 s a f x b)). Qed.
Lemma lem3792237 {A : Type'} (P : Prop) (Q : A -> Prop) : (term110 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3792238 {_98585 : Type'} (P : Prop) (Q : _98585 -> Prop) : (term110 _98585 P Q) = (term109 _98585 P Q).
Proof. exact (@lem3792237 _98585 P Q). Qed.
Lemma lem3792239 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term295 _98584 _98585 c s a f x b) = (term296 _98584 _98585 c s a f x b).
Proof. exact (@lem3792238 _98585 (term255 _98584 _98585 s b a f x c) (term275 _98584 _98585 s a f x b)). Qed.
Lemma lem3792240 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term297 _98584 _98585 s a f x b x') = (term273 _98584 _98585 s x' a f x b).
Proof. exact (eq_refl (term297 _98584 _98585 s a f x b x')). Qed.
Lemma lem3792241 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term298 _98584 _98585 s a f x b) = (term275 _98584 _98585 s a f x b).
Proof. exact (fun_ext (fun x' : _98585 => @lem3792240 _98584 _98585 s x' a f x b)). Qed.
Lemma lem3792242 {_98585 : Type'} : (@ex _98585) = (@ex _98585).
Proof. exact (eq_refl (@ex _98585)). Qed.
Lemma lem3792243 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term299 _98584 _98585 s a f x b) = (term276 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792242 _98585) (@lem3792241 _98584 _98585 s a f x b)). Qed.
Lemma lem3792244 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term289 _98584 _98585 s b a f x c) = (term289 _98584 _98585 s b a f x c).
Proof. exact (eq_refl (term289 _98584 _98585 s b a f x c)). Qed.
Lemma lem3792245 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term295 _98584 _98585 c s a f x b) = (term291 _98584 _98585 c s a f x b).
Proof. exact (MK_COMB (@lem3792244 _98584 _98585 s b a f x c) (@lem3792243 _98584 _98585 s a f x b)). Qed.
Lemma lem3792246 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3792247 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term300 _98584 _98585 c s a f x b) = (term301 _98584 _98585 c s a f x b).
Proof. exact (MK_COMB (@lem3792246) (@lem3792245 _98584 _98585 c s a f x b)). Qed.
Lemma lem3792248 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term297 _98584 _98585 s a f x b x') = (term273 _98584 _98585 s x' a f x b).
Proof. exact (eq_refl (term297 _98584 _98585 s a f x b x')). Qed.
Lemma lem3792249 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term289 _98584 _98585 s b a f x c) = (term289 _98584 _98585 s b a f x c).
Proof. exact (eq_refl (term289 _98584 _98585 s b a f x c)). Qed.
Lemma lem3792250 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term302 _98584 _98585 c s a f x b x') = (term303 _98584 _98585 c s x' a f x b).
Proof. exact (MK_COMB (@lem3792249 _98584 _98585 s b a f x c) (@lem3792248 _98584 _98585 s x' a f x b)). Qed.
Lemma lem3792251 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term304 _98584 _98585 c s a f x b) = (term305 _98584 _98585 c s a f x b).
Proof. exact (fun_ext (fun x' : _98585 => @lem3792250 _98584 _98585 c s x' a f x b)). Qed.
Lemma lem3792252 {_98585 : Type'} : (@ex _98585) = (@ex _98585).
Proof. exact (eq_refl (@ex _98585)). Qed.
Lemma lem3792253 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term296 _98584 _98585 c s a f x b) = (term306 _98584 _98585 c s a f x b).
Proof. exact (MK_COMB (@lem3792252 _98585) (@lem3792251 _98584 _98585 c s a f x b)). Qed.
Lemma lem3792254 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : ((term295 _98584 _98585 c s a f x b) = (term296 _98584 _98585 c s a f x b)) = ((term291 _98584 _98585 c s a f x b) = (term306 _98584 _98585 c s a f x b)).
Proof. exact (MK_COMB (@lem3792247 _98584 _98585 c s a f x b) (@lem3792253 _98584 _98585 c s a f x b)). Qed.
Lemma lem3792255 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term291 _98584 _98585 c s a f x b) = (term306 _98584 _98585 c s a f x b).
Proof. exact (EQ_MP (@lem3792254 _98584 _98585 c s a f x b) (@lem3792239 _98584 _98585 c s a f x b)). Qed.
Lemma lem3792256 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term293 _98584 _98585 s a f x b) = (term307 _98584 _98585 s a f x b).
Proof. exact (fun_ext (fun c : _98584 => @lem3792255 _98584 _98585 c s a f x b)). Qed.
Lemma lem3792257 {_98584 : Type'} : (@ex _98584) = (@ex _98584).
Proof. exact (eq_refl (@ex _98584)). Qed.
Lemma lem3792258 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term294 _98584 _98585 s a f x b) = (term308 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792257 _98584) (@lem3792256 _98584 _98585 s a f x b)). Qed.
Lemma lem3792259 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term277 _98584 _98585 s a f x b) = (term308 _98584 _98585 s a f x b).
Proof. exact (TRANS (@lem3792235 _98584 _98585 s a f x b) (@lem3792258 _98584 _98585 s a f x b)). Qed.
Lemma lem3792260 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term216 _98584 _98585 s a f x b) = (term308 _98584 _98585 s a f x b).
Proof. exact (TRANS (@lem3792211 _98584 _98585 s a f x b) (@lem3792259 _98584 _98585 s a f x b)). Qed.
Lemma lem3792261 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3792262 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term218 _98584 _98585 s a f x b) = (term309 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792261) (@lem3792260 _98584 _98585 s a f x b)). Qed.
Lemma lem3792264 {A : Type'} (P : A -> Prop) (Q : Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3792265 {_98585 : Type'} (P : _98585 -> Prop) (Q : Prop) : (term260 _98585 P Q) = (term261 _98585 P Q).
Proof. exact (@lem3792264 _98585 P Q). Qed.
Lemma lem3792266 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term310 _98584 _98585 s x c b) = (term311 _98584 _98585 s x c b).
Proof. exact (@lem3792265 _98585 (term157 _98585 s x) (term72 _98584 c b)). Qed.
Lemma lem3792267 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term312 _98585 s x x') = (term73 _98585 s x' x).
Proof. exact (eq_refl (term312 _98585 s x x')). Qed.
Lemma lem3792268 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term313 _98585 s x) = (term157 _98585 s x).
Proof. exact (fun_ext (fun x' : _98585 => @lem3792267 _98585 s x' x)). Qed.
Lemma lem3792269 {_98585 : Type'} : (@ex _98585) = (@ex _98585).
Proof. exact (eq_refl (@ex _98585)). Qed.
Lemma lem3792270 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term314 _98585 s x) = (term158 _98585 s x).
Proof. exact (MK_COMB (@lem3792269 _98585) (@lem3792268 _98585 s x)). Qed.
Lemma lem3792271 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3792272 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term315 _98585 s x) = (term162 _98585 s x).
Proof. exact (MK_COMB (@lem3792271) (@lem3792270 _98585 s x)). Qed.
Lemma lem3792273 {_98584 : Type'} (c : _98584) (b : _98584) : (term72 _98584 c b) = (term72 _98584 c b).
Proof. exact (eq_refl (term72 _98584 c b)). Qed.
Lemma lem3792274 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term310 _98584 _98585 s x c b) = (term164 _98584 _98585 s x c b).
Proof. exact (MK_COMB (@lem3792272 _98585 s x) (@lem3792273 _98584 c b)). Qed.
Lemma lem3792275 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3792276 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term316 _98584 _98585 s x c b) = (term317 _98584 _98585 s x c b).
Proof. exact (MK_COMB (@lem3792275) (@lem3792274 _98584 _98585 s x c b)). Qed.
Lemma lem3792277 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term312 _98585 s x x') = (term73 _98585 s x' x).
Proof. exact (eq_refl (term312 _98585 s x x')). Qed.
Lemma lem3792278 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3792279 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term318 _98585 s x x') = (term319 _98585 s x' x).
Proof. exact (MK_COMB (@lem3792278) (@lem3792277 _98585 s x' x)). Qed.
Lemma lem3792280 {_98584 : Type'} (c : _98584) (b : _98584) : (term72 _98584 c b) = (term72 _98584 c b).
Proof. exact (eq_refl (term72 _98584 c b)). Qed.
Lemma lem3792281 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) (c : _98584) (b : _98584) : (term320 _98584 _98585 s x x' c b) = (term321 _98584 _98585 s x' x c b).
Proof. exact (MK_COMB (@lem3792279 _98585 s x' x) (@lem3792280 _98584 c b)). Qed.
Lemma lem3792282 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term322 _98584 _98585 s x c b) = (term323 _98584 _98585 s x c b).
Proof. exact (fun_ext (fun x' : _98585 => @lem3792281 _98584 _98585 s x' x c b)). Qed.
Lemma lem3792283 {_98585 : Type'} : (@ex _98585) = (@ex _98585).
Proof. exact (eq_refl (@ex _98585)). Qed.
Lemma lem3792284 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term311 _98584 _98585 s x c b) = (term324 _98584 _98585 s x c b).
Proof. exact (MK_COMB (@lem3792283 _98585) (@lem3792282 _98584 _98585 s x c b)). Qed.
Lemma lem3792285 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : ((term310 _98584 _98585 s x c b) = (term311 _98584 _98585 s x c b)) = ((term164 _98584 _98585 s x c b) = (term324 _98584 _98585 s x c b)).
Proof. exact (MK_COMB (@lem3792276 _98584 _98585 s x c b) (@lem3792284 _98584 _98585 s x c b)). Qed.
Lemma lem3792286 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term164 _98584 _98585 s x c b) = (term324 _98584 _98585 s x c b).
Proof. exact (EQ_MP (@lem3792285 _98584 _98585 s x c b) (@lem3792266 _98584 _98585 s x c b)). Qed.
Lemma lem3792287 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3792288 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term170 _98584 _98585 s x c b) = (term325 _98584 _98585 s x c b).
Proof. exact (MK_COMB (@lem3792287) (@lem3792286 _98584 _98585 s x c b)). Qed.
Lemma lem3792289 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term168 _98584 _98585 a f x c) = (term168 _98584 _98585 a f x c).
Proof. exact (eq_refl (term168 _98584 _98585 a f x c)). Qed.
Lemma lem3792290 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term172 _98584 _98585 s b a f x c) = (term326 _98584 _98585 s b a f x c).
Proof. exact (MK_COMB (@lem3792288 _98584 _98585 s x c b) (@lem3792289 _98584 _98585 a f x c)). Qed.
Lemma lem3792292 {A : Type'} (P : A -> Prop) (Q : Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3792293 {_98585 : Type'} (P : _98585 -> Prop) (Q : Prop) : (term260 _98585 P Q) = (term261 _98585 P Q).
Proof. exact (@lem3792292 _98585 P Q). Qed.
Lemma lem3792294 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term327 _98584 _98585 s b a f x c) = (term328 _98584 _98585 s b a f x c).
Proof. exact (@lem3792293 _98585 (term323 _98584 _98585 s x c b) (term168 _98584 _98585 a f x c)). Qed.
Lemma lem3792295 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) (c : _98584) (b : _98584) : (term329 _98584 _98585 s x c b x') = (term321 _98584 _98585 s x' x c b).
Proof. exact (eq_refl (term329 _98584 _98585 s x c b x')). Qed.
Lemma lem3792296 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term330 _98584 _98585 s x c b) = (term323 _98584 _98585 s x c b).
Proof. exact (fun_ext (fun x' : _98585 => @lem3792295 _98584 _98585 s x' x c b)). Qed.
Lemma lem3792297 {_98585 : Type'} : (@ex _98585) = (@ex _98585).
Proof. exact (eq_refl (@ex _98585)). Qed.
Lemma lem3792298 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term331 _98584 _98585 s x c b) = (term324 _98584 _98585 s x c b).
Proof. exact (MK_COMB (@lem3792297 _98585) (@lem3792296 _98584 _98585 s x c b)). Qed.
Lemma lem3792299 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3792300 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term332 _98584 _98585 s x c b) = (term325 _98584 _98585 s x c b).
Proof. exact (MK_COMB (@lem3792299) (@lem3792298 _98584 _98585 s x c b)). Qed.
Lemma lem3792301 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term168 _98584 _98585 a f x c) = (term168 _98584 _98585 a f x c).
Proof. exact (eq_refl (term168 _98584 _98585 a f x c)). Qed.
Lemma lem3792302 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term327 _98584 _98585 s b a f x c) = (term326 _98584 _98585 s b a f x c).
Proof. exact (MK_COMB (@lem3792300 _98584 _98585 s x c b) (@lem3792301 _98584 _98585 a f x c)). Qed.
Lemma lem3792303 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3792304 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term333 _98584 _98585 s b a f x c) = (term334 _98584 _98585 s b a f x c).
Proof. exact (MK_COMB (@lem3792303) (@lem3792302 _98584 _98585 s b a f x c)). Qed.
Lemma lem3792305 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) (c : _98584) (b : _98584) : (term329 _98584 _98585 s x c b x') = (term321 _98584 _98585 s x' x c b).
Proof. exact (eq_refl (term329 _98584 _98585 s x c b x')). Qed.
Lemma lem3792306 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3792307 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) (c : _98584) (b : _98584) : (term335 _98584 _98585 s x c b x') = (term336 _98584 _98585 s x' x c b).
Proof. exact (MK_COMB (@lem3792306) (@lem3792305 _98584 _98585 s x' x c b)). Qed.
Lemma lem3792308 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term168 _98584 _98585 a f x c) = (term168 _98584 _98585 a f x c).
Proof. exact (eq_refl (term168 _98584 _98585 a f x c)). Qed.
Lemma lem3792309 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term337 _98584 _98585 s b x' a f x c) = (term338 _98584 _98585 s x' b a f x c).
Proof. exact (MK_COMB (@lem3792307 _98584 _98585 s x' x c b) (@lem3792308 _98584 _98585 a f x c)). Qed.
Lemma lem3792310 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term339 _98584 _98585 s b a f x c) = (term340 _98584 _98585 s b a f x c).
Proof. exact (fun_ext (fun x' : _98585 => @lem3792309 _98584 _98585 s x' b a f x c)). Qed.
Lemma lem3792311 {_98585 : Type'} : (@ex _98585) = (@ex _98585).
Proof. exact (eq_refl (@ex _98585)). Qed.
Lemma lem3792312 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term328 _98584 _98585 s b a f x c) = (term341 _98584 _98585 s b a f x c).
Proof. exact (MK_COMB (@lem3792311 _98585) (@lem3792310 _98584 _98585 s b a f x c)). Qed.
Lemma lem3792313 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : ((term327 _98584 _98585 s b a f x c) = (term328 _98584 _98585 s b a f x c)) = ((term326 _98584 _98585 s b a f x c) = (term341 _98584 _98585 s b a f x c)).
Proof. exact (MK_COMB (@lem3792304 _98584 _98585 s b a f x c) (@lem3792312 _98584 _98585 s b a f x c)). Qed.
Lemma lem3792314 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term326 _98584 _98585 s b a f x c) = (term341 _98584 _98585 s b a f x c).
Proof. exact (EQ_MP (@lem3792313 _98584 _98585 s b a f x c) (@lem3792294 _98584 _98585 s b a f x c)). Qed.
Lemma lem3792315 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term172 _98584 _98585 s b a f x c) = (term341 _98584 _98585 s b a f x c).
Proof. exact (TRANS (@lem3792290 _98584 _98585 s b a f x c) (@lem3792314 _98584 _98585 s b a f x c)). Qed.
Lemma lem3792316 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term182 _98584 _98585 s b a f x) = (term342 _98584 _98585 s b a f x).
Proof. exact (fun_ext (fun c : _98584 => @lem3792315 _98584 _98585 s b a f x c)). Qed.
Lemma lem3792317 {_98584 : Type'} : (@all _98584) = (@all _98584).
Proof. exact (eq_refl (@all _98584)). Qed.
Lemma lem3792318 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term183 _98584 _98585 s b a f x) = (term343 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3792317 _98584) (@lem3792316 _98584 _98585 s b a f x)). Qed.
Lemma lem3792320 {A B : Type'} (P : type1413 A B) : (term344 A B P) = (term345 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3792321 {_98584 _98585 : Type'} (P : type1413 _98584 _98585) : (term344 _98584 _98585 P) = (term345 _98584 _98585 P).
Proof. exact (@lem3792320 _98584 _98585 P). Qed.
Lemma lem3792322 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term346 _98584 _98585 s b a f x) = (term347 _98584 _98585 s b a f x).
Proof. exact (@lem3792321 _98584 _98585 (term348 _98584 _98585 s b a f x)). Qed.
Lemma lem3792323 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term349 _98584 _98585 s b a f x c) = (term340 _98584 _98585 s b a f x c).
Proof. exact (eq_refl (term349 _98584 _98585 s b a f x c)). Qed.
Lemma lem3792324 {_98585 : Type'} (x' : _98585) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem3792325 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) (x' : _98585) : (term350 _98584 _98585 s b a f x c x') = (term351 _98584 _98585 s b a f x c x').
Proof. exact (MK_COMB (@lem3792323 _98584 _98585 s b a f x c) (@lem3792324 _98585 x')). Qed.
Lemma lem3792326 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term351 _98584 _98585 s b a f x c x') = (term338 _98584 _98585 s x' b a f x c).
Proof. exact (eq_refl (term351 _98584 _98585 s b a f x c x')). Qed.
Lemma lem3792327 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term350 _98584 _98585 s b a f x c x') = (term338 _98584 _98585 s x' b a f x c).
Proof. exact (TRANS (@lem3792325 _98584 _98585 s b a f x c x') (@lem3792326 _98584 _98585 s x' b a f x c)). Qed.
Lemma lem3792328 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term352 _98584 _98585 s b a f x c) = (term340 _98584 _98585 s b a f x c).
Proof. exact (fun_ext (fun x' : _98585 => @lem3792327 _98584 _98585 s x' b a f x c)). Qed.
Lemma lem3792329 {_98585 : Type'} : (@ex _98585) = (@ex _98585).
Proof. exact (eq_refl (@ex _98585)). Qed.
Lemma lem3792330 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term353 _98584 _98585 s b a f x c) = (term341 _98584 _98585 s b a f x c).
Proof. exact (MK_COMB (@lem3792329 _98585) (@lem3792328 _98584 _98585 s b a f x c)). Qed.
Lemma lem3792331 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term354 _98584 _98585 s b a f x) = (term342 _98584 _98585 s b a f x).
Proof. exact (fun_ext (fun c : _98584 => @lem3792330 _98584 _98585 s b a f x c)). Qed.
Lemma lem3792332 {_98584 : Type'} : (@all _98584) = (@all _98584).
Proof. exact (eq_refl (@all _98584)). Qed.
Lemma lem3792333 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term346 _98584 _98585 s b a f x) = (term343 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3792332 _98584) (@lem3792331 _98584 _98585 s b a f x)). Qed.
Lemma lem3792334 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3792335 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term355 _98584 _98585 s b a f x) = (term356 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3792334) (@lem3792333 _98584 _98585 s b a f x)). Qed.
Lemma lem3792336 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term349 _98584 _98585 s b a f x c) = (term340 _98584 _98585 s b a f x c).
Proof. exact (eq_refl (term349 _98584 _98585 s b a f x c)). Qed.
Lemma lem3792337 {_98584 _98585 : Type'} (x' : _98584 -> _98585) (c : _98584) : (x' c) = (x' c).
Proof. exact (eq_refl (x' c)). Qed.
Lemma lem3792338 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (x' : _98584 -> _98585) (c : _98584) : (term357 _98584 _98585 s b a f x x' c) = (term358 _98584 _98585 s b a f x x' c).
Proof. exact (MK_COMB (@lem3792336 _98584 _98585 s b a f x c) (@lem3792337 _98584 _98585 x' c)). Qed.
Lemma lem3792339 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term358 _98584 _98585 s b a f x x' c) = (term359 _98584 _98585 s x' b a f x c).
Proof. exact (eq_refl (term358 _98584 _98585 s b a f x x' c)). Qed.
Lemma lem3792340 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term357 _98584 _98585 s b a f x x' c) = (term359 _98584 _98585 s x' b a f x c).
Proof. exact (TRANS (@lem3792338 _98584 _98585 s b a f x x' c) (@lem3792339 _98584 _98585 s x' b a f x c)). Qed.
Lemma lem3792341 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term360 _98584 _98585 s b a f x x') = (term361 _98584 _98585 s x' b a f x).
Proof. exact (fun_ext (fun c : _98584 => @lem3792340 _98584 _98585 s x' b a f x c)). Qed.
Lemma lem3792342 {_98584 : Type'} : (@all _98584) = (@all _98584).
Proof. exact (eq_refl (@all _98584)). Qed.
Lemma lem3792343 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term362 _98584 _98585 s b a f x x') = (term363 _98584 _98585 s x' b a f x).
Proof. exact (MK_COMB (@lem3792342 _98584) (@lem3792341 _98584 _98585 s x' b a f x)). Qed.
Lemma lem3792344 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term364 _98584 _98585 s b a f x) = (term365 _98584 _98585 s b a f x).
Proof. exact (fun_ext (fun x' : _98584 -> _98585 => @lem3792343 _98584 _98585 s x' b a f x)). Qed.
Lemma lem3792345 {_98584 _98585 : Type'} : (@ex (_98584 -> _98585)) = (@ex (_98584 -> _98585)).
Proof. exact (eq_refl (@ex (_98584 -> _98585))). Qed.
Lemma lem3792346 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term347 _98584 _98585 s b a f x) = (term366 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3792345 _98584 _98585) (@lem3792344 _98584 _98585 s b a f x)). Qed.
Lemma lem3792347 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : ((term346 _98584 _98585 s b a f x) = (term347 _98584 _98585 s b a f x)) = ((term343 _98584 _98585 s b a f x) = (term366 _98584 _98585 s b a f x)).
Proof. exact (MK_COMB (@lem3792335 _98584 _98585 s b a f x) (@lem3792346 _98584 _98585 s b a f x)). Qed.
Lemma lem3792348 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term343 _98584 _98585 s b a f x) = (term366 _98584 _98585 s b a f x).
Proof. exact (EQ_MP (@lem3792347 _98584 _98585 s b a f x) (@lem3792322 _98584 _98585 s b a f x)). Qed.
Lemma lem3792349 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term183 _98584 _98585 s b a f x) = (term366 _98584 _98585 s b a f x).
Proof. exact (TRANS (@lem3792318 _98584 _98585 s b a f x) (@lem3792348 _98584 _98585 s b a f x)). Qed.
Lemma lem3792350 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term146 _98585 s x) = (term146 _98585 s x).
Proof. exact (eq_refl (term146 _98585 s x)). Qed.
Lemma lem3792351 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term187 _98584 _98585 s b a f x) = (term367 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3792350 _98585 s x) (@lem3792349 _98584 _98585 s b a f x)). Qed.
Lemma lem3792353 {A : Type'} (P : Prop) (Q : A -> Prop) : (term368 A P Q) = (term369 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3792354 {_98584 _98585 : Type'} (P : Prop) (Q : type572 _98584 _98585) : (term370 _98584 _98585 P Q) = (term371 _98584 _98585 P Q).
Proof. exact (@lem3792353 (_98584 -> _98585) P Q). Qed.
Lemma lem3792355 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term372 _98584 _98585 s b a f x) = (term373 _98584 _98585 s b a f x).
Proof. exact (@lem3792354 _98584 _98585 (term374 _98585 s x) (term365 _98584 _98585 s b a f x)). Qed.
Lemma lem3792356 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term375 _98584 _98585 s b a f x x') = (term363 _98584 _98585 s x' b a f x).
Proof. exact (eq_refl (term375 _98584 _98585 s b a f x x')). Qed.
Lemma lem3792357 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term376 _98584 _98585 s b a f x) = (term365 _98584 _98585 s b a f x).
Proof. exact (fun_ext (fun x' : _98584 -> _98585 => @lem3792356 _98584 _98585 s x' b a f x)). Qed.
Lemma lem3792358 {_98584 _98585 : Type'} : (@ex (_98584 -> _98585)) = (@ex (_98584 -> _98585)).
Proof. exact (eq_refl (@ex (_98584 -> _98585))). Qed.
Lemma lem3792359 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term377 _98584 _98585 s b a f x) = (term366 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3792358 _98584 _98585) (@lem3792357 _98584 _98585 s b a f x)). Qed.
Lemma lem3792360 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term146 _98585 s x) = (term146 _98585 s x).
Proof. exact (eq_refl (term146 _98585 s x)). Qed.
Lemma lem3792361 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term372 _98584 _98585 s b a f x) = (term367 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3792360 _98585 s x) (@lem3792359 _98584 _98585 s b a f x)). Qed.
Lemma lem3792362 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3792363 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term378 _98584 _98585 s b a f x) = (term379 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3792362) (@lem3792361 _98584 _98585 s b a f x)). Qed.
Lemma lem3792364 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term375 _98584 _98585 s b a f x x') = (term363 _98584 _98585 s x' b a f x).
Proof. exact (eq_refl (term375 _98584 _98585 s b a f x x')). Qed.
Lemma lem3792365 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term146 _98585 s x) = (term146 _98585 s x).
Proof. exact (eq_refl (term146 _98585 s x)). Qed.
Lemma lem3792366 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term380 _98584 _98585 s b a f x x') = (term381 _98584 _98585 s x' b a f x).
Proof. exact (MK_COMB (@lem3792365 _98585 s x) (@lem3792364 _98584 _98585 s x' b a f x)). Qed.
Lemma lem3792367 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term382 _98584 _98585 s b a f x) = (term383 _98584 _98585 s b a f x).
Proof. exact (fun_ext (fun x' : _98584 -> _98585 => @lem3792366 _98584 _98585 s x' b a f x)). Qed.
Lemma lem3792368 {_98584 _98585 : Type'} : (@ex (_98584 -> _98585)) = (@ex (_98584 -> _98585)).
Proof. exact (eq_refl (@ex (_98584 -> _98585))). Qed.
Lemma lem3792369 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term373 _98584 _98585 s b a f x) = (term384 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3792368 _98584 _98585) (@lem3792367 _98584 _98585 s b a f x)). Qed.
Lemma lem3792370 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : ((term372 _98584 _98585 s b a f x) = (term373 _98584 _98585 s b a f x)) = ((term367 _98584 _98585 s b a f x) = (term384 _98584 _98585 s b a f x)).
Proof. exact (MK_COMB (@lem3792363 _98584 _98585 s b a f x) (@lem3792369 _98584 _98585 s b a f x)). Qed.
Lemma lem3792371 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term367 _98584 _98585 s b a f x) = (term384 _98584 _98585 s b a f x).
Proof. exact (EQ_MP (@lem3792370 _98584 _98585 s b a f x) (@lem3792355 _98584 _98585 s b a f x)). Qed.
Lemma lem3792372 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term187 _98584 _98585 s b a f x) = (term384 _98584 _98585 s b a f x).
Proof. exact (TRANS (@lem3792351 _98584 _98585 s b a f x) (@lem3792371 _98584 _98585 s b a f x)). Qed.
Lemma lem3792373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3792374 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term210 _98584 _98585 s b a f x) = (term385 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3792373) (@lem3792372 _98584 _98585 s b a f x)). Qed.
Lemma lem3792375 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term244 _98584 _98585 s a f x b) = (term244 _98584 _98585 s a f x b).
Proof. exact (eq_refl (term244 _98584 _98585 s a f x b)). Qed.
Lemma lem3792376 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term245 _98584 _98585 s a f x b) = (term386 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792374 _98584 _98585 s b a f x) (@lem3792375 _98584 _98585 s a f x b)). Qed.
Lemma lem3792378 {A : Type'} (P : A -> Prop) (Q : Prop) : (term278 A P Q) = (term279 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3792379 {_98584 _98585 : Type'} (P : type572 _98584 _98585) (Q : Prop) : (term387 _98584 _98585 P Q) = (term388 _98584 _98585 P Q).
Proof. exact (@lem3792378 (_98584 -> _98585) P Q). Qed.
Lemma lem3792380 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term389 _98584 _98585 s a f x b) = (term390 _98584 _98585 s a f x b).
Proof. exact (@lem3792379 _98584 _98585 (term383 _98584 _98585 s b a f x) (term244 _98584 _98585 s a f x b)). Qed.
Lemma lem3792381 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term391 _98584 _98585 s b a f x x') = (term381 _98584 _98585 s x' b a f x).
Proof. exact (eq_refl (term391 _98584 _98585 s b a f x x')). Qed.
Lemma lem3792382 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term392 _98584 _98585 s b a f x) = (term383 _98584 _98585 s b a f x).
Proof. exact (fun_ext (fun x' : _98584 -> _98585 => @lem3792381 _98584 _98585 s x' b a f x)). Qed.
Lemma lem3792383 {_98584 _98585 : Type'} : (@ex (_98584 -> _98585)) = (@ex (_98584 -> _98585)).
Proof. exact (eq_refl (@ex (_98584 -> _98585))). Qed.
Lemma lem3792384 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term393 _98584 _98585 s b a f x) = (term384 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3792383 _98584 _98585) (@lem3792382 _98584 _98585 s b a f x)). Qed.
Lemma lem3792385 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3792386 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term394 _98584 _98585 s b a f x) = (term385 _98584 _98585 s b a f x).
Proof. exact (MK_COMB (@lem3792385) (@lem3792384 _98584 _98585 s b a f x)). Qed.
Lemma lem3792387 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term244 _98584 _98585 s a f x b) = (term244 _98584 _98585 s a f x b).
Proof. exact (eq_refl (term244 _98584 _98585 s a f x b)). Qed.
Lemma lem3792388 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term389 _98584 _98585 s a f x b) = (term386 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792386 _98584 _98585 s b a f x) (@lem3792387 _98584 _98585 s a f x b)). Qed.
Lemma lem3792389 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3792390 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term395 _98584 _98585 s a f x b) = (term396 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792389) (@lem3792388 _98584 _98585 s a f x b)). Qed.
Lemma lem3792391 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term391 _98584 _98585 s b a f x x') = (term381 _98584 _98585 s x' b a f x).
Proof. exact (eq_refl (term391 _98584 _98585 s b a f x x')). Qed.
Lemma lem3792392 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3792393 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term397 _98584 _98585 s b a f x x') = (term398 _98584 _98585 s x' b a f x).
Proof. exact (MK_COMB (@lem3792392) (@lem3792391 _98584 _98585 s x' b a f x)). Qed.
Lemma lem3792394 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term244 _98584 _98585 s a f x b) = (term244 _98584 _98585 s a f x b).
Proof. exact (eq_refl (term244 _98584 _98585 s a f x b)). Qed.
Lemma lem3792395 {_98584 _98585 : Type'} (x' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term399 _98584 _98585 x' s a f x b) = (term400 _98584 _98585 x' s a f x b).
Proof. exact (MK_COMB (@lem3792393 _98584 _98585 s x' b a f x) (@lem3792394 _98584 _98585 s a f x b)). Qed.
Lemma lem3792396 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term401 _98584 _98585 s a f x b) = (term402 _98584 _98585 s a f x b).
Proof. exact (fun_ext (fun x' : _98584 -> _98585 => @lem3792395 _98584 _98585 x' s a f x b)). Qed.
Lemma lem3792397 {_98584 _98585 : Type'} : (@ex (_98584 -> _98585)) = (@ex (_98584 -> _98585)).
Proof. exact (eq_refl (@ex (_98584 -> _98585))). Qed.
Lemma lem3792398 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term390 _98584 _98585 s a f x b) = (term403 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792397 _98584 _98585) (@lem3792396 _98584 _98585 s a f x b)). Qed.
Lemma lem3792399 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : ((term389 _98584 _98585 s a f x b) = (term390 _98584 _98585 s a f x b)) = ((term386 _98584 _98585 s a f x b) = (term403 _98584 _98585 s a f x b)).
Proof. exact (MK_COMB (@lem3792390 _98584 _98585 s a f x b) (@lem3792398 _98584 _98585 s a f x b)). Qed.
Lemma lem3792400 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term386 _98584 _98585 s a f x b) = (term403 _98584 _98585 s a f x b).
Proof. exact (EQ_MP (@lem3792399 _98584 _98585 s a f x b) (@lem3792380 _98584 _98585 s a f x b)). Qed.
Lemma lem3792401 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term245 _98584 _98585 s a f x b) = (term403 _98584 _98585 s a f x b).
Proof. exact (TRANS (@lem3792376 _98584 _98585 s a f x b) (@lem3792400 _98584 _98585 s a f x b)). Qed.
Lemma lem3792402 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term246 _98584 _98585 s a f x b) = (term404 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792262 _98584 _98585 s a f x b) (@lem3792401 _98584 _98585 s a f x b)). Qed.
Lemma lem3792406 {A : Type'} (P : A -> Prop) (Q : Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3792407 {_98584 : Type'} (P : _98584 -> Prop) (Q : Prop) : (term260 _98584 P Q) = (term261 _98584 P Q).
Proof. exact (@lem3792406 _98584 P Q). Qed.
Lemma lem3792408 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term405 _98584 _98585 s a f x b) = (term406 _98584 _98585 s a f x b).
Proof. exact (@lem3792407 _98584 (term307 _98584 _98585 s a f x b) (term403 _98584 _98585 s a f x b)). Qed.
Lemma lem3792409 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term407 _98584 _98585 s a f x b c) = (term306 _98584 _98585 c s a f x b).
Proof. exact (eq_refl (term407 _98584 _98585 s a f x b c)). Qed.
Lemma lem3792410 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term408 _98584 _98585 s a f x b) = (term307 _98584 _98585 s a f x b).
Proof. exact (fun_ext (fun c : _98584 => @lem3792409 _98584 _98585 c s a f x b)). Qed.
Lemma lem3792411 {_98584 : Type'} : (@ex _98584) = (@ex _98584).
Proof. exact (eq_refl (@ex _98584)). Qed.
Lemma lem3792412 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term409 _98584 _98585 s a f x b) = (term308 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792411 _98584) (@lem3792410 _98584 _98585 s a f x b)). Qed.
Lemma lem3792413 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3792414 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term410 _98584 _98585 s a f x b) = (term309 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792413) (@lem3792412 _98584 _98585 s a f x b)). Qed.
Lemma lem3792415 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term403 _98584 _98585 s a f x b) = (term403 _98584 _98585 s a f x b).
Proof. exact (eq_refl (term403 _98584 _98585 s a f x b)). Qed.
Lemma lem3792416 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term405 _98584 _98585 s a f x b) = (term404 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792414 _98584 _98585 s a f x b) (@lem3792415 _98584 _98585 s a f x b)). Qed.
Lemma lem3792417 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3792418 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term411 _98584 _98585 s a f x b) = (term412 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792417) (@lem3792416 _98584 _98585 s a f x b)). Qed.
Lemma lem3792419 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term407 _98584 _98585 s a f x b c) = (term306 _98584 _98585 c s a f x b).
Proof. exact (eq_refl (term407 _98584 _98585 s a f x b c)). Qed.
Lemma lem3792420 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3792421 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term413 _98584 _98585 s a f x b c) = (term414 _98584 _98585 c s a f x b).
Proof. exact (MK_COMB (@lem3792420) (@lem3792419 _98584 _98585 c s a f x b)). Qed.
Lemma lem3792422 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term403 _98584 _98585 s a f x b) = (term403 _98584 _98585 s a f x b).
Proof. exact (eq_refl (term403 _98584 _98585 s a f x b)). Qed.
Lemma lem3792423 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term415 _98584 _98585 c s a f x b) = (term416 _98584 _98585 c s a f x b).
Proof. exact (MK_COMB (@lem3792421 _98584 _98585 c s a f x b) (@lem3792422 _98584 _98585 s a f x b)). Qed.
Lemma lem3792424 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term417 _98584 _98585 s a f x b) = (term418 _98584 _98585 s a f x b).
Proof. exact (fun_ext (fun c : _98584 => @lem3792423 _98584 _98585 c s a f x b)). Qed.
Lemma lem3792425 {_98584 : Type'} : (@ex _98584) = (@ex _98584).
Proof. exact (eq_refl (@ex _98584)). Qed.
Lemma lem3792426 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term406 _98584 _98585 s a f x b) = (term419 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792425 _98584) (@lem3792424 _98584 _98585 s a f x b)). Qed.
Lemma lem3792427 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : ((term405 _98584 _98585 s a f x b) = (term406 _98584 _98585 s a f x b)) = ((term404 _98584 _98585 s a f x b) = (term419 _98584 _98585 s a f x b)).
Proof. exact (MK_COMB (@lem3792418 _98584 _98585 s a f x b) (@lem3792426 _98584 _98585 s a f x b)). Qed.
Lemma lem3792428 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term404 _98584 _98585 s a f x b) = (term419 _98584 _98585 s a f x b).
Proof. exact (EQ_MP (@lem3792427 _98584 _98585 s a f x b) (@lem3792408 _98584 _98585 s a f x b)). Qed.
Lemma lem3792432 {A : Type'} (P : A -> Prop) (Q : Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3792433 {_98585 : Type'} (P : _98585 -> Prop) (Q : Prop) : (term260 _98585 P Q) = (term261 _98585 P Q).
Proof. exact (@lem3792432 _98585 P Q). Qed.
Lemma lem3792434 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term420 _98584 _98585 c s a f x b) = (term421 _98584 _98585 c s a f x b).
Proof. exact (@lem3792433 _98585 (term305 _98584 _98585 c s a f x b) (term403 _98584 _98585 s a f x b)). Qed.
Lemma lem3792435 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term422 _98584 _98585 c s a f x b x') = (term303 _98584 _98585 c s x' a f x b).
Proof. exact (eq_refl (term422 _98584 _98585 c s a f x b x')). Qed.
Lemma lem3792436 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term423 _98584 _98585 c s a f x b) = (term305 _98584 _98585 c s a f x b).
Proof. exact (fun_ext (fun x' : _98585 => @lem3792435 _98584 _98585 c s x' a f x b)). Qed.
Lemma lem3792437 {_98585 : Type'} : (@ex _98585) = (@ex _98585).
Proof. exact (eq_refl (@ex _98585)). Qed.
Lemma lem3792438 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term424 _98584 _98585 c s a f x b) = (term306 _98584 _98585 c s a f x b).
Proof. exact (MK_COMB (@lem3792437 _98585) (@lem3792436 _98584 _98585 c s a f x b)). Qed.
Lemma lem3792439 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3792440 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term425 _98584 _98585 c s a f x b) = (term414 _98584 _98585 c s a f x b).
Proof. exact (MK_COMB (@lem3792439) (@lem3792438 _98584 _98585 c s a f x b)). Qed.
Lemma lem3792441 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term403 _98584 _98585 s a f x b) = (term403 _98584 _98585 s a f x b).
Proof. exact (eq_refl (term403 _98584 _98585 s a f x b)). Qed.
Lemma lem3792442 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term420 _98584 _98585 c s a f x b) = (term416 _98584 _98585 c s a f x b).
Proof. exact (MK_COMB (@lem3792440 _98584 _98585 c s a f x b) (@lem3792441 _98584 _98585 s a f x b)). Qed.
Lemma lem3792443 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3792444 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term426 _98584 _98585 c s a f x b) = (term427 _98584 _98585 c s a f x b).
Proof. exact (MK_COMB (@lem3792443) (@lem3792442 _98584 _98585 c s a f x b)). Qed.
Lemma lem3792445 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term422 _98584 _98585 c s a f x b x') = (term303 _98584 _98585 c s x' a f x b).
Proof. exact (eq_refl (term422 _98584 _98585 c s a f x b x')). Qed.
Lemma lem3792446 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3792447 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term428 _98584 _98585 c s a f x b x') = (term429 _98584 _98585 c s x' a f x b).
Proof. exact (MK_COMB (@lem3792446) (@lem3792445 _98584 _98585 c s x' a f x b)). Qed.
Lemma lem3792448 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term403 _98584 _98585 s a f x b) = (term403 _98584 _98585 s a f x b).
Proof. exact (eq_refl (term403 _98584 _98585 s a f x b)). Qed.
Lemma lem3792449 {_98584 _98585 : Type'} (c : _98584) (x' : _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term430 _98584 _98585 c x' s a f x b) = (term431 _98584 _98585 c x' s a f x b).
Proof. exact (MK_COMB (@lem3792447 _98584 _98585 c s x' a f x b) (@lem3792448 _98584 _98585 s a f x b)). Qed.
Lemma lem3792450 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term432 _98584 _98585 c s a f x b) = (term433 _98584 _98585 c s a f x b).
Proof. exact (fun_ext (fun x' : _98585 => @lem3792449 _98584 _98585 c x' s a f x b)). Qed.
Lemma lem3792451 {_98585 : Type'} : (@ex _98585) = (@ex _98585).
Proof. exact (eq_refl (@ex _98585)). Qed.
Lemma lem3792452 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term421 _98584 _98585 c s a f x b) = (term434 _98584 _98585 c s a f x b).
Proof. exact (MK_COMB (@lem3792451 _98585) (@lem3792450 _98584 _98585 c s a f x b)). Qed.
Lemma lem3792453 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : ((term420 _98584 _98585 c s a f x b) = (term421 _98584 _98585 c s a f x b)) = ((term416 _98584 _98585 c s a f x b) = (term434 _98584 _98585 c s a f x b)).
Proof. exact (MK_COMB (@lem3792444 _98584 _98585 c s a f x b) (@lem3792452 _98584 _98585 c s a f x b)). Qed.
Lemma lem3792454 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term416 _98584 _98585 c s a f x b) = (term434 _98584 _98585 c s a f x b).
Proof. exact (EQ_MP (@lem3792453 _98584 _98585 c s a f x b) (@lem3792434 _98584 _98585 c s a f x b)). Qed.
Lemma lem3792456 {A : Type'} (P : Prop) (Q : A -> Prop) : (term368 A P Q) = (term369 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3792457 {_98584 _98585 : Type'} (P : Prop) (Q : type572 _98584 _98585) : (term370 _98584 _98585 P Q) = (term371 _98584 _98585 P Q).
Proof. exact (@lem3792456 (_98584 -> _98585) P Q). Qed.
Lemma lem3792458 {_98584 _98585 : Type'} (c : _98584) (x' : _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term435 _98584 _98585 c x' s a f x b) = (term436 _98584 _98585 c x' s a f x b).
Proof. exact (@lem3792457 _98584 _98585 (term303 _98584 _98585 c s x' a f x b) (term402 _98584 _98585 s a f x b)). Qed.
Lemma lem3792459 {_98584 _98585 : Type'} (x' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term437 _98584 _98585 s a f x b x') = (term400 _98584 _98585 x' s a f x b).
Proof. exact (eq_refl (term437 _98584 _98585 s a f x b x')). Qed.
Lemma lem3792460 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term438 _98584 _98585 s a f x b) = (term402 _98584 _98585 s a f x b).
Proof. exact (fun_ext (fun x' : _98584 -> _98585 => @lem3792459 _98584 _98585 x' s a f x b)). Qed.
Lemma lem3792461 {_98584 _98585 : Type'} : (@ex (_98584 -> _98585)) = (@ex (_98584 -> _98585)).
Proof. exact (eq_refl (@ex (_98584 -> _98585))). Qed.
Lemma lem3792462 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term439 _98584 _98585 s a f x b) = (term403 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792461 _98584 _98585) (@lem3792460 _98584 _98585 s a f x b)). Qed.
Lemma lem3792463 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term429 _98584 _98585 c s x' a f x b) = (term429 _98584 _98585 c s x' a f x b).
Proof. exact (eq_refl (term429 _98584 _98585 c s x' a f x b)). Qed.
Lemma lem3792464 {_98584 _98585 : Type'} (c : _98584) (x' : _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term435 _98584 _98585 c x' s a f x b) = (term431 _98584 _98585 c x' s a f x b).
Proof. exact (MK_COMB (@lem3792463 _98584 _98585 c s x' a f x b) (@lem3792462 _98584 _98585 s a f x b)). Qed.
Lemma lem3792465 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3792466 {_98584 _98585 : Type'} (c : _98584) (x' : _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term440 _98584 _98585 c x' s a f x b) = (term441 _98584 _98585 c x' s a f x b).
Proof. exact (MK_COMB (@lem3792465) (@lem3792464 _98584 _98585 c x' s a f x b)). Qed.
Lemma lem3792467 {_98584 _98585 : Type'} (x' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term437 _98584 _98585 s a f x b x') = (term400 _98584 _98585 x' s a f x b).
Proof. exact (eq_refl (term437 _98584 _98585 s a f x b x')). Qed.
Lemma lem3792468 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term429 _98584 _98585 c s x' a f x b) = (term429 _98584 _98585 c s x' a f x b).
Proof. exact (eq_refl (term429 _98584 _98585 c s x' a f x b)). Qed.
Lemma lem3792469 {_98584 _98585 : Type'} (c : _98584) (x' : _98585) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term442 _98584 _98585 c x' s a f x b x'') = (term443 _98584 _98585 c x' x'' s a f x b).
Proof. exact (MK_COMB (@lem3792468 _98584 _98585 c s x' a f x b) (@lem3792467 _98584 _98585 x'' s a f x b)). Qed.
Lemma lem3792470 {_98584 _98585 : Type'} (c : _98584) (x' : _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term444 _98584 _98585 c x' s a f x b) = (term445 _98584 _98585 c x' s a f x b).
Proof. exact (fun_ext (fun x'' : _98584 -> _98585 => @lem3792469 _98584 _98585 c x' x'' s a f x b)). Qed.
Lemma lem3792471 {_98584 _98585 : Type'} : (@ex (_98584 -> _98585)) = (@ex (_98584 -> _98585)).
Proof. exact (eq_refl (@ex (_98584 -> _98585))). Qed.
Lemma lem3792472 {_98584 _98585 : Type'} (c : _98584) (x' : _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term436 _98584 _98585 c x' s a f x b) = (term446 _98584 _98585 c x' s a f x b).
Proof. exact (MK_COMB (@lem3792471 _98584 _98585) (@lem3792470 _98584 _98585 c x' s a f x b)). Qed.
Lemma lem3792473 {_98584 _98585 : Type'} (c : _98584) (x' : _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : ((term435 _98584 _98585 c x' s a f x b) = (term436 _98584 _98585 c x' s a f x b)) = ((term431 _98584 _98585 c x' s a f x b) = (term446 _98584 _98585 c x' s a f x b)).
Proof. exact (MK_COMB (@lem3792466 _98584 _98585 c x' s a f x b) (@lem3792472 _98584 _98585 c x' s a f x b)). Qed.
Lemma lem3792474 {_98584 _98585 : Type'} (c : _98584) (x' : _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term431 _98584 _98585 c x' s a f x b) = (term446 _98584 _98585 c x' s a f x b).
Proof. exact (EQ_MP (@lem3792473 _98584 _98585 c x' s a f x b) (@lem3792458 _98584 _98585 c x' s a f x b)). Qed.
Lemma lem3792475 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term433 _98584 _98585 c s a f x b) = (term447 _98584 _98585 c s a f x b).
Proof. exact (fun_ext (fun x' : _98585 => @lem3792474 _98584 _98585 c x' s a f x b)). Qed.
Lemma lem3792476 {_98585 : Type'} : (@ex _98585) = (@ex _98585).
Proof. exact (eq_refl (@ex _98585)). Qed.
Lemma lem3792477 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term434 _98584 _98585 c s a f x b) = (term448 _98584 _98585 c s a f x b).
Proof. exact (MK_COMB (@lem3792476 _98585) (@lem3792475 _98584 _98585 c s a f x b)). Qed.
Lemma lem3792478 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term416 _98584 _98585 c s a f x b) = (term448 _98584 _98585 c s a f x b).
Proof. exact (TRANS (@lem3792454 _98584 _98585 c s a f x b) (@lem3792477 _98584 _98585 c s a f x b)). Qed.
Lemma lem3792479 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term418 _98584 _98585 s a f x b) = (term449 _98584 _98585 s a f x b).
Proof. exact (fun_ext (fun c : _98584 => @lem3792478 _98584 _98585 c s a f x b)). Qed.
Lemma lem3792480 {_98584 : Type'} : (@ex _98584) = (@ex _98584).
Proof. exact (eq_refl (@ex _98584)). Qed.
Lemma lem3792481 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term419 _98584 _98585 s a f x b) = (term450 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792480 _98584) (@lem3792479 _98584 _98585 s a f x b)). Qed.
Lemma lem3792482 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term404 _98584 _98585 s a f x b) = (term450 _98584 _98585 s a f x b).
Proof. exact (TRANS (@lem3792428 _98584 _98585 s a f x b) (@lem3792481 _98584 _98585 s a f x b)). Qed.
Lemma lem3792483 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term246 _98584 _98585 s a f x b) = (term450 _98584 _98585 s a f x b).
Proof. exact (TRANS (@lem3792402 _98584 _98585 s a f x b) (@lem3792482 _98584 _98585 s a f x b)). Qed.
Lemma lem3792484 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term220 _98584 _98585 s a f x b) = (term450 _98584 _98585 s a f x b).
Proof. exact (TRANS (@lem3792164 _98584 _98585 s a f x b) (@lem3792483 _98584 _98585 s a f x b)). Qed.
Lemma lem3792485 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term144 _98584 _98585 s a f x b) = (term450 _98584 _98585 s a f x b).
Proof. exact (TRANS (@lem3791833 _98584 _98585 s a f x b) (@lem3792484 _98584 _98585 s a f x b)). Qed.
Lemma lem3792486 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term144 _98584 _98585 s a f x b) : term450 _98584 _98585 s a f x b.
Proof. exact (EQ_MP (@lem3792485 _98584 _98585 s a f x b) (@lem3791701 _98584 _98585 s a f x b h1)). Qed.
Lemma lem3792487 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term448 _98584 _98585 c s a f x b) : term448 _98584 _98585 c s a f x b.
Proof. exact (h1). Qed.
Lemma lem3792488 {_98584 _98585 : Type'} (c : _98584) (x' : _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term446 _98584 _98585 c x' s a f x b) : term446 _98584 _98585 c x' s a f x b.
Proof. exact (h1). Qed.
Lemma lem3792489 {_98584 _98585 : Type'} (c : _98584) (x' : _98585) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term443 _98584 _98585 c x' x'' s a f x b) : term443 _98584 _98585 c x' x'' s a f x b.
Proof. exact (h1). Qed.
Lemma lem3792498 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (a = (f x b)) = (a = (f x b)).
Proof. exact (eq_refl (a = (f x b))). Qed.
Lemma lem3792511 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term148 _98585 s x' x) = (term148 _98585 s x' x).
Proof. exact (eq_refl (term148 _98585 s x' x)). Qed.
Lemma lem3792512 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term159 _98585 s x) = (term159 _98585 s x).
Proof. exact (fun_ext (fun x' : _98585 => @lem3792511 _98585 s x' x)). Qed.
Lemma lem3792513 {_98585 : Type'} : (@all _98585) = (@all _98585).
Proof. exact (eq_refl (@all _98585)). Qed.
Lemma lem3792514 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term160 _98585 s x) = (term160 _98585 s x).
Proof. exact (MK_COMB (@lem3792513 _98585) (@lem3792512 _98585 s x)). Qed.
Lemma lem3792527 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term227 _98585 s x' x) = (term227 _98585 s x' x).
Proof. exact (eq_refl (term227 _98585 s x' x)). Qed.
Lemma lem3792528 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term225 _98585 s x) = (term225 _98585 s x).
Proof. exact (fun_ext (fun x' : _98585 => @lem3792527 _98585 s x' x)). Qed.
Lemma lem3792529 {_98585 : Type'} : (@all _98585) = (@all _98585).
Proof. exact (eq_refl (@all _98585)). Qed.
Lemma lem3792530 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term237 _98585 s x) = (term237 _98585 s x).
Proof. exact (MK_COMB (@lem3792529 _98585) (@lem3792528 _98585 s x)). Qed.
Lemma lem3792531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3792532 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term239 _98585 s x) = (term239 _98585 s x).
Proof. exact (MK_COMB (@lem3792531) (@lem3792530 _98585 s x)). Qed.
Lemma lem3792533 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term242 _98585 s x) = (term242 _98585 s x).
Proof. exact (MK_COMB (@lem3792532 _98585 s x) (@lem3792514 _98585 s x)). Qed.
Lemma lem3792534 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3792535 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term243 _98585 s x) = (term243 _98585 s x).
Proof. exact (MK_COMB (@lem3792534) (@lem3792533 _98585 s x)). Qed.
Lemma lem3792536 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term244 _98584 _98585 s a f x b) = (term244 _98584 _98585 s a f x b).
Proof. exact (MK_COMB (@lem3792535 _98585 s x) (@lem3792498 _98584 _98585 a f x b)). Qed.
Lemma lem3792577 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term359 _98584 _98585 s x'' b a f x c) = (term359 _98584 _98585 s x'' b a f x c).
Proof. exact (eq_refl (term359 _98584 _98585 s x'' b a f x c)). Qed.
Lemma lem3792578 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term361 _98584 _98585 s x'' b a f x) = (term361 _98584 _98585 s x'' b a f x).
Proof. exact (fun_ext (fun c : _98584 => @lem3792577 _98584 _98585 s x'' b a f x c)). Qed.
Lemma lem3792579 {_98584 : Type'} : (@all _98584) = (@all _98584).
Proof. exact (eq_refl (@all _98584)). Qed.
Lemma lem3792580 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term363 _98584 _98585 s x'' b a f x) = (term363 _98584 _98585 s x'' b a f x).
Proof. exact (MK_COMB (@lem3792579 _98584) (@lem3792578 _98584 _98585 s x'' b a f x)). Qed.
Lemma lem3792587 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term146 _98585 s x) = (term146 _98585 s x).
Proof. exact (eq_refl (term146 _98585 s x)). Qed.
Lemma lem3792588 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term381 _98584 _98585 s x'' b a f x) = (term381 _98584 _98585 s x'' b a f x).
Proof. exact (MK_COMB (@lem3792587 _98585 s x) (@lem3792580 _98584 _98585 s x'' b a f x)). Qed.
Lemma lem3792589 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3792590 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term398 _98584 _98585 s x'' b a f x) = (term398 _98584 _98585 s x'' b a f x).
Proof. exact (MK_COMB (@lem3792589) (@lem3792588 _98584 _98585 s x'' b a f x)). Qed.
Lemma lem3792591 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term400 _98584 _98585 x'' s a f x b) = (term400 _98584 _98585 x'' s a f x b).
Proof. exact (MK_COMB (@lem3792590 _98584 _98585 s x'' b a f x) (@lem3792536 _98584 _98585 s a f x b)). Qed.
Lemma lem3792634 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term273 _98584 _98585 s x' a f x b) = (term273 _98584 _98585 s x' a f x b).
Proof. exact (eq_refl (term273 _98584 _98585 s x' a f x b)). Qed.
Lemma lem3792643 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (a = (f x c)) = (a = (f x c)).
Proof. exact (eq_refl (a = (f x c))). Qed.
Lemma lem3792648 {_98584 : Type'} (c : _98584) (b : _98584) : (c = b) = (c = b).
Proof. exact (eq_refl (c = b)). Qed.
Lemma lem3792661 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term148 _98585 s x' x) = (term148 _98585 s x' x).
Proof. exact (eq_refl (term148 _98585 s x' x)). Qed.
Lemma lem3792662 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term159 _98585 s x) = (term159 _98585 s x).
Proof. exact (fun_ext (fun x' : _98585 => @lem3792661 _98585 s x' x)). Qed.
Lemma lem3792663 {_98585 : Type'} : (@all _98585) = (@all _98585).
Proof. exact (eq_refl (@all _98585)). Qed.
Lemma lem3792664 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term160 _98585 s x) = (term160 _98585 s x).
Proof. exact (MK_COMB (@lem3792663 _98585) (@lem3792662 _98585 s x)). Qed.
Lemma lem3792665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3792666 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term166 _98585 s x) = (term166 _98585 s x).
Proof. exact (MK_COMB (@lem3792665) (@lem3792664 _98585 s x)). Qed.
Lemma lem3792667 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term167 _98584 _98585 s x c b) = (term167 _98584 _98585 s x c b).
Proof. exact (MK_COMB (@lem3792666 _98585 s x) (@lem3792648 _98584 c b)). Qed.
Lemma lem3792668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3792669 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x : _98585) (c : _98584) (b : _98584) : (term174 _98584 _98585 s x c b) = (term174 _98584 _98585 s x c b).
Proof. exact (MK_COMB (@lem3792668) (@lem3792667 _98584 _98585 s x c b)). Qed.
Lemma lem3792670 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term175 _98584 _98585 s b a f x c) = (term175 _98584 _98585 s b a f x c).
Proof. exact (MK_COMB (@lem3792669 _98584 _98585 s x c b) (@lem3792643 _98584 _98585 a f x c)). Qed.
Lemma lem3792675 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term69 _98585 s x) = (term69 _98585 s x).
Proof. exact (eq_refl (term69 _98585 s x)). Qed.
Lemma lem3792676 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term255 _98584 _98585 s b a f x c) = (term255 _98584 _98585 s b a f x c).
Proof. exact (MK_COMB (@lem3792675 _98585 s x) (@lem3792670 _98584 _98585 s b a f x c)). Qed.
Lemma lem3792677 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3792678 {_98584 _98585 : Type'} (s : _98585 -> Prop) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term289 _98584 _98585 s b a f x c) = (term289 _98584 _98585 s b a f x c).
Proof. exact (MK_COMB (@lem3792677) (@lem3792676 _98584 _98585 s b a f x c)). Qed.
Lemma lem3792679 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term303 _98584 _98585 c s x' a f x b) = (term303 _98584 _98585 c s x' a f x b).
Proof. exact (MK_COMB (@lem3792678 _98584 _98585 s b a f x c) (@lem3792634 _98584 _98585 s x' a f x b)). Qed.
Lemma lem3792680 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3792681 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term429 _98584 _98585 c s x' a f x b) = (term429 _98584 _98585 c s x' a f x b).
Proof. exact (MK_COMB (@lem3792680) (@lem3792679 _98584 _98585 c s x' a f x b)). Qed.
Lemma lem3792682 {_98584 _98585 : Type'} (c : _98584) (x' : _98585) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term443 _98584 _98585 c x' x'' s a f x b) = (term443 _98584 _98585 c x' x'' s a f x b).
Proof. exact (MK_COMB (@lem3792681 _98584 _98585 c s x' a f x b) (@lem3792591 _98584 _98585 x'' s a f x b)). Qed.
Lemma lem3792683 {_98584 _98585 : Type'} (c : _98584) (x' : _98585) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term443 _98584 _98585 c x' x'' s a f x b) : term443 _98584 _98585 c x' x'' s a f x b.
Proof. exact (EQ_MP (@lem3792682 _98584 _98585 c x' x'' s a f x b) (@lem3792489 _98584 _98585 c x' x'' s a f x b h1)). Qed.
Lemma lem3792684 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : term303 _98584 _98585 c s x' a f x b.
Proof. exact (h1). Qed.
Lemma lem3792685 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : term400 _98584 _98585 x'' s a f x b.
Proof. exact (h1). Qed.
Lemma lem3792686 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : term273 _98584 _98585 s x' a f x b.
Proof. exact (proj2 (@lem3792684 _98584 _98585 c s x' a f x b h1)). Qed.
Lemma lem3792687 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : term255 _98584 _98585 s b a f x c.
Proof. exact (proj1 (@lem3792684 _98584 _98585 c s x' a f x b h1)). Qed.
Lemma lem3792688 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : term175 _98584 _98585 s b a f x c.
Proof. exact (proj2 (@lem3792687 _98584 _98585 c s x' a f x b h1)). Qed.
Lemma lem3792691 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : term167 _98584 _98585 s x c b.
Proof. exact (proj1 (@lem3792688 _98584 _98585 c s x' a f x b h1)). Qed.
Lemma lem3792693 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : term160 _98585 s x.
Proof. exact (proj1 (@lem3792691 _98584 _98585 c s x' a f x b h1)). Qed.
Lemma lem3792694 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) (h1 : term191 _98585 s x' x) : term191 _98585 s x' x.
Proof. exact (h1). Qed.
Lemma lem3792696 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) (h1 : term191 _98585 s x' x) : term451 _98585 s x' x.
Proof. exact (proj2 (@lem3792694 _98585 s x' x h1)). Qed.
Lemma lem3792697 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) (h1 : term191 _98585 s x' x) : term452 _98585 s x' x.
Proof. exact (proj1 (@lem3792694 _98585 s x' x h1)). Qed.
Lemma lem3792704 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : term244 _98584 _98585 s a f x b.
Proof. exact (proj2 (@lem3792685 _98584 _98585 x'' s a f x b h1)). Qed.
Lemma lem3792705 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : term381 _98584 _98585 s x'' b a f x.
Proof. exact (proj1 (@lem3792685 _98584 _98585 x'' s a f x b h1)). Qed.
Lemma lem3792707 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : term242 _98585 s x.
Proof. exact (proj1 (@lem3792704 _98584 _98585 x'' s a f x b h1)). Qed.
Lemma lem3792708 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : term160 _98585 s x.
Proof. exact (proj2 (@lem3792707 _98584 _98585 x'' s a f x b h1)). Qed.
Lemma lem3792709 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : term237 _98585 s x.
Proof. exact (proj1 (@lem3792707 _98584 _98585 x'' s a f x b h1)). Qed.
Lemma lem3792711 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (h1 : term363 _98584 _98585 s x'' b a f x) : term363 _98584 _98585 s x'' b a f x.
Proof. exact (h1). Qed.
Lemma lem3792740 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') : term374 _98585 s x'.
Proof. exact (h1). Qed.
Lemma lem3792744 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3792773 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') : term374 _98585 s x'.
Proof. exact (h1). Qed.
Lemma lem3792777 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3792793 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term148 _98585 s x' x) = (term148 _98585 s x' x).
Proof. exact (eq_refl (term148 _98585 s x' x)). Qed.
Lemma lem3792794 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term159 _98585 s x) = (term159 _98585 s x).
Proof. exact (fun_ext (fun x' : _98585 => @lem3792793 _98585 s x' x)). Qed.
Lemma lem3792795 {_98585 : Type'} : (@all _98585) = (@all _98585).
Proof. exact (eq_refl (@all _98585)). Qed.
Lemma lem3792797 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term160 _98585 s x) = (term160 _98585 s x).
Proof. exact (MK_COMB (@lem3792795 _98585) (@lem3792794 _98585 s x)). Qed.
Lemma lem3792798 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : term160 _98585 s x.
Proof. exact (EQ_MP (@lem3792797 _98585 s x) (@lem3792693 _98584 _98585 c s x' a f x b h1)). Qed.
Lemma lem3792806 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) : term72 _98585 x' x.
Proof. exact (h1). Qed.
Lemma lem3792810 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3792839 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) : term72 _98585 x' x.
Proof. exact (h1). Qed.
Lemma lem3792843 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3792872 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term168 _98584 _98585 a f x b) : term168 _98584 _98585 a f x b.
Proof. exact (h1). Qed.
Lemma lem3792884 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term227 _98585 s x' x) = (term227 _98585 s x' x).
Proof. exact (eq_refl (term227 _98585 s x' x)). Qed.
Lemma lem3792885 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term225 _98585 s x) = (term225 _98585 s x).
Proof. exact (fun_ext (fun x' : _98585 => @lem3792884 _98585 s x' x)). Qed.
Lemma lem3792886 {_98585 : Type'} : (@all _98585) = (@all _98585).
Proof. exact (eq_refl (@all _98585)). Qed.
Lemma lem3792888 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term237 _98585 s x) = (term237 _98585 s x).
Proof. exact (MK_COMB (@lem3792886 _98585) (@lem3792885 _98585 s x)). Qed.
Lemma lem3792889 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : term237 _98585 s x.
Proof. exact (EQ_MP (@lem3792888 _98585 s x) (@lem3792709 _98584 _98585 x'' s a f x b h1)). Qed.
Lemma lem3792906 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) (h1 : term374 _98585 s x) : term374 _98585 s x.
Proof. exact (h1). Qed.
Lemma lem3792931 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) : (term148 _98585 s x' x) = (term148 _98585 s x' x).
Proof. exact (eq_refl (term148 _98585 s x' x)). Qed.
Lemma lem3792932 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term159 _98585 s x) = (term159 _98585 s x).
Proof. exact (fun_ext (fun x' : _98585 => @lem3792931 _98585 s x' x)). Qed.
Lemma lem3792933 {_98585 : Type'} : (@all _98585) = (@all _98585).
Proof. exact (eq_refl (@all _98585)). Qed.
Lemma lem3792935 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term160 _98585 s x) = (term160 _98585 s x).
Proof. exact (MK_COMB (@lem3792933 _98585) (@lem3792932 _98585 s x)). Qed.
Lemma lem3792936 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : term160 _98585 s x.
Proof. exact (EQ_MP (@lem3792935 _98585 s x) (@lem3792708 _98584 _98585 x'' s a f x b h1)). Qed.
Lemma lem3792938 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term168 _98584 _98585 a f x c) = (term168 _98584 _98585 a f x c).
Proof. exact (eq_refl (term168 _98584 _98585 a f x c)). Qed.
Lemma lem3792955 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (x : _98585) (c : _98584) (b : _98584) : (term453 _98584 _98585 s x'' x c b) = (term454 _98584 _98585 s x'' x c b).
Proof. exact (@lem19699 (term455 _98584 _98585 s x'' c) (term456 _98584 _98585 x'' c x) (term72 _98584 c b)). Qed.
Lemma lem3792956 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3792957 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (x : _98585) (c : _98584) (b : _98584) : (term457 _98584 _98585 s x'' x c b) = (term458 _98584 _98585 s x'' x c b).
Proof. exact (MK_COMB (@lem3792956) (@lem3792955 _98584 _98585 s x'' x c b)). Qed.
Lemma lem3792958 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term359 _98584 _98585 s x'' b a f x c) = (term459 _98584 _98585 s x'' b a f x c).
Proof. exact (MK_COMB (@lem3792957 _98584 _98585 s x'' x c b) (@lem3792938 _98584 _98585 a f x c)). Qed.
Lemma lem3792965 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term459 _98584 _98585 s x'' b a f x c) = (term460 _98584 _98585 s x'' b a f x c).
Proof. exact (@lem19699 (term461 _98584 _98585 s x'' c b) (term462 _98584 _98585 x'' x c b) (term168 _98584 _98585 a f x c)). Qed.
Lemma lem3792966 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term359 _98584 _98585 s x'' b a f x c) = (term460 _98584 _98585 s x'' b a f x c).
Proof. exact (TRANS (@lem3792958 _98584 _98585 s x'' b a f x c) (@lem3792965 _98584 _98585 s x'' b a f x c)). Qed.
Lemma lem3792967 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term361 _98584 _98585 s x'' b a f x) = (term463 _98584 _98585 s x'' b a f x).
Proof. exact (fun_ext (fun c : _98584 => @lem3792966 _98584 _98585 s x'' b a f x c)). Qed.
Lemma lem3792968 {_98584 : Type'} : (@all _98584) = (@all _98584).
Proof. exact (eq_refl (@all _98584)). Qed.
Lemma lem3792970 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term363 _98584 _98585 s x'' b a f x) = (term464 _98584 _98585 s x'' b a f x).
Proof. exact (MK_COMB (@lem3792968 _98584) (@lem3792967 _98584 _98585 s x'' b a f x)). Qed.
Lemma lem3792971 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (h1 : term363 _98584 _98585 s x'' b a f x) : term464 _98584 _98585 s x'' b a f x.
Proof. exact (EQ_MP (@lem3792970 _98584 _98585 s x'' b a f x) (@lem3792711 _98584 _98585 s x'' b a f x h1)). Qed.
Lemma lem3792978 {_98584 _98585 : Type'} (_43489 : _98585) (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : term230 _98585 s x _43489.
Proof. exact (@lem3792798 _98584 _98585 c s x' a f x b h1 _43489). Qed.
Lemma lem3792979 {_98585 : Type'} (s : _98585 -> Prop) (_43489 : _98585) (x : _98585) : (term230 _98585 s x _43489) = (term148 _98585 s _43489 x).
Proof. exact (eq_refl (term230 _98585 s x _43489)). Qed.
Lemma lem3792987 {_98584 _98585 : Type'} (_43492 : _98585) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : term226 _98585 s x _43492.
Proof. exact (@lem3792889 _98584 _98585 x'' s a f x b h1 _43492). Qed.
Lemma lem3792988 {_98585 : Type'} (s : _98585 -> Prop) (_43492 : _98585) (x : _98585) : (term226 _98585 s x _43492) = (term227 _98585 s _43492 x).
Proof. exact (eq_refl (term226 _98585 s x _43492)). Qed.
Lemma lem3792996 {_98584 _98585 : Type'} (_43495 : _98585) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : term230 _98585 s x _43495.
Proof. exact (@lem3792936 _98584 _98585 x'' s a f x b h1 _43495). Qed.
Lemma lem3792997 {_98585 : Type'} (s : _98585 -> Prop) (_43495 : _98585) (x : _98585) : (term230 _98585 s x _43495) = (term148 _98585 s _43495 x).
Proof. exact (eq_refl (term230 _98585 s x _43495)). Qed.
Lemma lem3792999 {_98584 _98585 : Type'} (_43496 : _98584) (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (h1 : term363 _98584 _98585 s x'' b a f x) : term465 _98584 _98585 s x'' b a f x _43496.
Proof. exact (@lem3792971 _98584 _98585 s x'' b a f x h1 _43496). Qed.
Lemma lem3793000 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term465 _98584 _98585 s x'' b a f x _43496) = (term460 _98584 _98585 s x'' b a f x _43496).
Proof. exact (eq_refl (term465 _98584 _98585 s x'' b a f x _43496)). Qed.
Lemma lem3793001 {_98584 _98585 : Type'} (_43496 : _98584) (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (h1 : term363 _98584 _98585 s x'' b a f x) : term460 _98584 _98585 s x'' b a f x _43496.
Proof. exact (EQ_MP (@lem3793000 _98584 _98585 s x'' b a f x _43496) (@lem3792999 _98584 _98585 _43496 s x'' b a f x h1)). Qed.
Lemma lem3793002 {_98584 _98585 : Type'} (_43496 : _98584) (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (h1 : term363 _98584 _98585 s x'' b a f x) : term466 _98584 _98585 x'' b a f x _43496.
Proof. exact (proj2 (@lem3793001 _98584 _98585 _43496 s x'' b a f x h1)). Qed.
Lemma lem3793003 {_98584 _98585 : Type'} (_43496 : _98584) (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (h1 : term363 _98584 _98585 s x'' b a f x) : term467 _98584 _98585 s x'' b a f x _43496.
Proof. exact (proj1 (@lem3793001 _98584 _98585 _43496 s x'' b a f x h1)). Qed.
Lemma lem3793017 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') : term374 _98585 s x'.
Proof. exact (h1). Qed.
Lemma lem3793019 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3793033 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') : term374 _98585 s x'.
Proof. exact (h1). Qed.
Lemma lem3793035 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3793049 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) : term72 _98585 x' x.
Proof. exact (h1). Qed.
Lemma lem3793051 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3793065 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) : term72 _98585 x' x.
Proof. exact (h1). Qed.
Lemma lem3793067 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3793071 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : a = (f x c).
Proof. exact (proj2 (@lem3792688 _98584 _98585 c s x' a f x b h1)). Qed.
Lemma lem3793079 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : c = b.
Proof. exact (proj2 (@lem3792691 _98584 _98585 c s x' a f x b h1)). Qed.
Lemma lem3793081 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term168 _98584 _98585 a f x b) : term168 _98584 _98585 a f x b.
Proof. exact (h1). Qed.
Lemma lem3793097 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) (h1 : term374 _98585 s x) : term374 _98585 s x.
Proof. exact (h1). Qed.
Lemma lem3793099 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : a = (f x b).
Proof. exact (proj2 (@lem3792704 _98584 _98585 x'' s a f x b h1)). Qed.
Lemma lem3793122 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term467 _98584 _98585 s x'' b a f x _43496) = (term468 _98584 _98585 s x'' b a f x _43496).
Proof. exact (@lem3791037 (term455 _98584 _98585 s x'' _43496) (term72 _98584 _43496 b) (term168 _98584 _98585 a f x _43496)). Qed.
Lemma lem3793123 {_98584 _98585 : Type'} (_43496 : _98584) (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (h1 : term363 _98584 _98585 s x'' b a f x) : term468 _98584 _98585 s x'' b a f x _43496.
Proof. exact (EQ_MP (@lem3793122 _98584 _98585 s x'' b a f x _43496) (@lem3793003 _98584 _98585 _43496 s x'' b a f x h1)). Qed.
Lemma lem3793134 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term466 _98584 _98585 x'' b a f x _43496) = (term469 _98584 _98585 x'' b a f x _43496).
Proof. exact (@lem3791037 (term456 _98584 _98585 x'' _43496 x) (term72 _98584 _43496 b) (term168 _98584 _98585 a f x _43496)). Qed.
Lemma lem3793135 {_98584 _98585 : Type'} (_43496 : _98584) (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (h1 : term363 _98584 _98585 s x'' b a f x) : term469 _98584 _98585 x'' b a f x _43496.
Proof. exact (EQ_MP (@lem3793134 _98584 _98585 x'' b a f x _43496) (@lem3793002 _98584 _98585 _43496 s x'' b a f x h1)). Qed.
Lemma lem3793204 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') : term374 _98585 s x'.
Proof. exact (h1). Qed.
Lemma lem3793218 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3793274 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') : term374 _98585 s x'.
Proof. exact (h1). Qed.
Lemma lem3793288 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3793359 {_98585 : Type'} (s : _98585 -> Prop) : (term470 _98585 s) = (term470 _98585 s).
Proof. exact (eq_refl (term470 _98585 s)). Qed.
Lemma lem3793360 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) (h1 : x' = x) : (term471 _98585 s x') = (term471 _98585 s x).
Proof. exact (MK_COMB (@lem3793359 _98585 s) (@lem3793035 _98585 x' x h1)). Qed.
Lemma lem3793361 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term471 _98585 s x) = (term374 _98585 s x).
Proof. exact (eq_refl (term471 _98585 s x)). Qed.
Lemma lem3793362 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) : (term472 _98585 s x') = (term472 _98585 s x').
Proof. exact (eq_refl (term472 _98585 s x')). Qed.
Lemma lem3793363 {_98585 : Type'} (x' : _98585) (s : _98585 -> Prop) (x : _98585) : ((term471 _98585 s x') = (term471 _98585 s x)) = ((term471 _98585 s x') = (term374 _98585 s x)).
Proof. exact (MK_COMB (@lem3793362 _98585 s x') (@lem3793361 _98585 s x)). Qed.
Lemma lem3793364 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) : (term471 _98585 s x') = (term374 _98585 s x').
Proof. exact (eq_refl (term471 _98585 s x')). Qed.
Lemma lem3793365 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3793366 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) : (term472 _98585 s x') = (term473 _98585 s x').
Proof. exact (MK_COMB (@lem3793365) (@lem3793364 _98585 s x')). Qed.
Lemma lem3793367 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term374 _98585 s x) = (term374 _98585 s x).
Proof. exact (eq_refl (term374 _98585 s x)). Qed.
Lemma lem3793368 {_98585 : Type'} (x' : _98585) (s : _98585 -> Prop) (x : _98585) : ((term471 _98585 s x') = (term374 _98585 s x)) = ((term374 _98585 s x') = (term374 _98585 s x)).
Proof. exact (MK_COMB (@lem3793366 _98585 s x') (@lem3793367 _98585 s x)). Qed.
Lemma lem3793369 {_98585 : Type'} (x' : _98585) (s : _98585 -> Prop) (x : _98585) : ((term471 _98585 s x') = (term471 _98585 s x)) = ((term374 _98585 s x') = (term374 _98585 s x)).
Proof. exact (TRANS (@lem3793363 _98585 x' s x) (@lem3793368 _98585 x' s x)). Qed.
Lemma lem3793370 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) (h1 : x' = x) : (term374 _98585 s x') = (term374 _98585 s x).
Proof. exact (EQ_MP (@lem3793369 _98585 x' s x) (@lem3793360 _98585 s x' x h1)). Qed.
Lemma lem3793496 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) (h1 : term374 _98585 s x') (h2 : x' = x) : term374 _98585 s x.
Proof. exact (EQ_MP (@lem3793370 _98585 s x' x h2) (@lem3793033 _98585 s x' h1)). Qed.
Lemma lem3793565 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) : term72 _98585 x' x.
Proof. exact (h1). Qed.
Lemma lem3793579 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3793621 {_98584 _98585 : Type'} (_43489 : _98585) (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : term148 _98585 s _43489 x.
Proof. exact (EQ_MP (@lem3792979 _98585 s _43489 x) (@lem3792978 _98584 _98585 _43489 c s x' a f x b h1)). Qed.
Lemma lem3793635 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) : term72 _98585 x' x.
Proof. exact (h1). Qed.
Lemma lem3793649 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3793720 {_98585 : Type'} (x : _98585) : (term474 _98585 x) = (term474 _98585 x).
Proof. exact (eq_refl (term474 _98585 x)). Qed.
Lemma lem3793721 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : x' = x) : (term475 _98585 x x') = (term476 _98585 x).
Proof. exact (MK_COMB (@lem3793720 _98585 x) (@lem3793067 _98585 x' x h1)). Qed.
Lemma lem3793722 {_98585 : Type'} (x : _98585) : (term476 _98585 x) = (term477 _98585 x).
Proof. exact (eq_refl (term476 _98585 x)). Qed.
Lemma lem3793723 {_98585 : Type'} (x : _98585) (x' : _98585) : (term478 _98585 x x') = (term478 _98585 x x').
Proof. exact (eq_refl (term478 _98585 x x')). Qed.
Lemma lem3793724 {_98585 : Type'} (x' : _98585) (x : _98585) : ((term475 _98585 x x') = (term476 _98585 x)) = ((term475 _98585 x x') = (term477 _98585 x)).
Proof. exact (MK_COMB (@lem3793723 _98585 x x') (@lem3793722 _98585 x)). Qed.
Lemma lem3793725 {_98585 : Type'} (x' : _98585) (x : _98585) : (term475 _98585 x x') = (term72 _98585 x' x).
Proof. exact (eq_refl (term475 _98585 x x')). Qed.
Lemma lem3793726 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3793727 {_98585 : Type'} (x' : _98585) (x : _98585) : (term478 _98585 x x') = (term479 _98585 x' x).
Proof. exact (MK_COMB (@lem3793726) (@lem3793725 _98585 x' x)). Qed.
Lemma lem3793728 {_98585 : Type'} (x : _98585) : (term477 _98585 x) = (term477 _98585 x).
Proof. exact (eq_refl (term477 _98585 x)). Qed.
Lemma lem3793729 {_98585 : Type'} (x' : _98585) (x : _98585) : ((term475 _98585 x x') = (term477 _98585 x)) = ((term72 _98585 x' x) = (term477 _98585 x)).
Proof. exact (MK_COMB (@lem3793727 _98585 x' x) (@lem3793728 _98585 x)). Qed.
Lemma lem3793730 {_98585 : Type'} (x' : _98585) (x : _98585) : ((term475 _98585 x x') = (term476 _98585 x)) = ((term72 _98585 x' x) = (term477 _98585 x)).
Proof. exact (TRANS (@lem3793724 _98585 x' x) (@lem3793729 _98585 x' x)). Qed.
Lemma lem3793731 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : x' = x) : (term72 _98585 x' x) = (term477 _98585 x).
Proof. exact (EQ_MP (@lem3793730 _98585 x' x) (@lem3793721 _98585 x' x h1)). Qed.
Lemma lem3793857 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) (h2 : x' = x) : term477 _98585 x.
Proof. exact (EQ_MP (@lem3793731 _98585 x' x h2) (@lem3793065 _98585 x' x h1)). Qed.
Lemma lem3793886 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) : (term480 _98584 _98585 a f x) = (term480 _98584 _98585 a f x).
Proof. exact (eq_refl (term480 _98584 _98585 a f x)). Qed.
Lemma lem3793887 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : (term481 _98584 _98585 a f x c) = (term481 _98584 _98585 a f x b).
Proof. exact (MK_COMB (@lem3793886 _98584 _98585 a f x) (@lem3793079 _98584 _98585 c s x' a f x b h1)). Qed.
Lemma lem3793888 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term481 _98584 _98585 a f x b) = (a = (f x b)).
Proof. exact (eq_refl (term481 _98584 _98585 a f x b)). Qed.
Lemma lem3793889 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term482 _98584 _98585 a f x c) = (term482 _98584 _98585 a f x c).
Proof. exact (eq_refl (term482 _98584 _98585 a f x c)). Qed.
Lemma lem3793890 {_98584 _98585 : Type'} (c : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : ((term481 _98584 _98585 a f x c) = (term481 _98584 _98585 a f x b)) = ((term481 _98584 _98585 a f x c) = (a = (f x b))).
Proof. exact (MK_COMB (@lem3793889 _98584 _98585 a f x c) (@lem3793888 _98584 _98585 a f x b)). Qed.
Lemma lem3793891 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term481 _98584 _98585 a f x c) = (a = (f x c)).
Proof. exact (eq_refl (term481 _98584 _98585 a f x c)). Qed.
Lemma lem3793892 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3793893 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (c : _98584) : (term482 _98584 _98585 a f x c) = (term483 _98584 _98585 a f x c).
Proof. exact (MK_COMB (@lem3793892) (@lem3793891 _98584 _98585 a f x c)). Qed.
Lemma lem3793894 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (a = (f x b)) = (a = (f x b)).
Proof. exact (eq_refl (a = (f x b))). Qed.
Lemma lem3793895 {_98584 _98585 : Type'} (c : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : ((term481 _98584 _98585 a f x c) = (a = (f x b))) = ((a = (f x c)) = (a = (f x b))).
Proof. exact (MK_COMB (@lem3793893 _98584 _98585 a f x c) (@lem3793894 _98584 _98585 a f x b)). Qed.
Lemma lem3793896 {_98584 _98585 : Type'} (c : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : ((term481 _98584 _98585 a f x c) = (term481 _98584 _98585 a f x b)) = ((a = (f x c)) = (a = (f x b))).
Proof. exact (TRANS (@lem3793890 _98584 _98585 c a f x b) (@lem3793895 _98584 _98585 c a f x b)). Qed.
Lemma lem3793897 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : (a = (f x c)) = (a = (f x b)).
Proof. exact (EQ_MP (@lem3793896 _98584 _98585 c a f x b) (@lem3793887 _98584 _98585 c s x' a f x b h1)). Qed.
Lemma lem3793898 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : a = (f x b).
Proof. exact (EQ_MP (@lem3793897 _98584 _98585 c s x' a f x b h1) (@lem3793071 _98584 _98585 c s x' a f x b h1)). Qed.
Lemma lem3793926 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term168 _98584 _98585 a f x b) : term168 _98584 _98585 a f x b.
Proof. exact (h1). Qed.
Lemma lem3793969 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term484 _98584 _98585 f x b) = (term484 _98584 _98585 f x b).
Proof. exact (eq_refl (term484 _98584 _98585 f x b)). Qed.
Lemma lem3793970 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : (term485 _98584 _98585 f x b a) = (term486 _98584 _98585 f x b).
Proof. exact (MK_COMB (@lem3793969 _98584 _98585 f x b) (@lem3793898 _98584 _98585 c s x' a f x b h1)). Qed.
Lemma lem3793971 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term486 _98584 _98585 f x b) = (term487 _98584 _98585 f x b).
Proof. exact (eq_refl (term486 _98584 _98585 f x b)). Qed.
Lemma lem3793972 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (a : _98584) : (term488 _98584 _98585 f x b a) = (term488 _98584 _98585 f x b a).
Proof. exact (eq_refl (term488 _98584 _98585 f x b a)). Qed.
Lemma lem3793973 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : ((term485 _98584 _98585 f x b a) = (term486 _98584 _98585 f x b)) = ((term485 _98584 _98585 f x b a) = (term487 _98584 _98585 f x b)).
Proof. exact (MK_COMB (@lem3793972 _98584 _98585 f x b a) (@lem3793971 _98584 _98585 f x b)). Qed.
Lemma lem3793974 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term485 _98584 _98585 f x b a) = (term168 _98584 _98585 a f x b).
Proof. exact (eq_refl (term485 _98584 _98585 f x b a)). Qed.
Lemma lem3793975 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3793976 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term488 _98584 _98585 f x b a) = (term489 _98584 _98585 a f x b).
Proof. exact (MK_COMB (@lem3793975) (@lem3793974 _98584 _98585 a f x b)). Qed.
Lemma lem3793977 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term487 _98584 _98585 f x b) = (term487 _98584 _98585 f x b).
Proof. exact (eq_refl (term487 _98584 _98585 f x b)). Qed.
Lemma lem3793978 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : ((term485 _98584 _98585 f x b a) = (term487 _98584 _98585 f x b)) = ((term168 _98584 _98585 a f x b) = (term487 _98584 _98585 f x b)).
Proof. exact (MK_COMB (@lem3793976 _98584 _98585 a f x b) (@lem3793977 _98584 _98585 f x b)). Qed.
Lemma lem3793979 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : ((term485 _98584 _98585 f x b a) = (term486 _98584 _98585 f x b)) = ((term168 _98584 _98585 a f x b) = (term487 _98584 _98585 f x b)).
Proof. exact (TRANS (@lem3793973 _98584 _98585 a f x b) (@lem3793978 _98584 _98585 a f x b)). Qed.
Lemma lem3793980 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : (term168 _98584 _98585 a f x b) = (term487 _98584 _98585 f x b).
Proof. exact (EQ_MP (@lem3793979 _98584 _98585 a f x b) (@lem3793970 _98584 _98585 c s x' a f x b h1)). Qed.
Lemma lem3793981 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term168 _98584 _98585 a f x b) (h2 : term303 _98584 _98585 c s x' a f x b) : term487 _98584 _98585 f x b.
Proof. exact (EQ_MP (@lem3793980 _98584 _98585 c s x' a f x b h2) (@lem3793926 _98584 _98585 a f x b h1)). Qed.
Lemma lem3794009 {_98584 _98585 : Type'} (_43492 : _98585) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : term227 _98585 s _43492 x.
Proof. exact (EQ_MP (@lem3792988 _98585 s _43492 x) (@lem3792987 _98584 _98585 _43492 x'' s a f x b h1)). Qed.
Lemma lem3794037 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) (h1 : term374 _98585 s x) : term374 _98585 s x.
Proof. exact (h1). Qed.
Lemma lem3794079 {_98584 _98585 : Type'} (_43495 : _98585) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : term148 _98585 s _43495 x.
Proof. exact (EQ_MP (@lem3792997 _98585 s _43495 x) (@lem3792996 _98584 _98585 _43495 x'' s a f x b h1)). Qed.
Lemma lem3794080 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term490 _98584 _98585 s x'' b f x _43496) = (term490 _98584 _98585 s x'' b f x _43496).
Proof. exact (eq_refl (term490 _98584 _98585 s x'' b f x _43496)). Qed.
Lemma lem3794081 {_98584 _98585 : Type'} (_43496 : _98584) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : (term491 _98584 _98585 s x'' b f x _43496 a) = (term492 _98584 _98585 s x'' _43496 f x b).
Proof. exact (MK_COMB (@lem3794080 _98584 _98585 s x'' b f x _43496) (@lem3793099 _98584 _98585 x'' s a f x b h1)). Qed.
Lemma lem3794082 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term492 _98584 _98585 s x'' _43496 f x b) = (term493 _98584 _98585 s x'' b f x _43496).
Proof. exact (eq_refl (term492 _98584 _98585 s x'' _43496 f x b)). Qed.
Lemma lem3794083 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) (a : _98584) : (term494 _98584 _98585 s x'' b f x _43496 a) = (term494 _98584 _98585 s x'' b f x _43496 a).
Proof. exact (eq_refl (term494 _98584 _98585 s x'' b f x _43496 a)). Qed.
Lemma lem3794084 {_98584 _98585 : Type'} (a : _98584) (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : ((term491 _98584 _98585 s x'' b f x _43496 a) = (term492 _98584 _98585 s x'' _43496 f x b)) = ((term491 _98584 _98585 s x'' b f x _43496 a) = (term493 _98584 _98585 s x'' b f x _43496)).
Proof. exact (MK_COMB (@lem3794083 _98584 _98585 s x'' b f x _43496 a) (@lem3794082 _98584 _98585 s x'' b f x _43496)). Qed.
Lemma lem3794085 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term491 _98584 _98585 s x'' b f x _43496 a) = (term468 _98584 _98585 s x'' b a f x _43496).
Proof. exact (eq_refl (term491 _98584 _98585 s x'' b f x _43496 a)). Qed.
Lemma lem3794086 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3794087 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term494 _98584 _98585 s x'' b f x _43496 a) = (term495 _98584 _98585 s x'' b a f x _43496).
Proof. exact (MK_COMB (@lem3794086) (@lem3794085 _98584 _98585 s x'' b a f x _43496)). Qed.
Lemma lem3794088 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term493 _98584 _98585 s x'' b f x _43496) = (term493 _98584 _98585 s x'' b f x _43496).
Proof. exact (eq_refl (term493 _98584 _98585 s x'' b f x _43496)). Qed.
Lemma lem3794089 {_98584 _98585 : Type'} (a : _98584) (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : ((term491 _98584 _98585 s x'' b f x _43496 a) = (term493 _98584 _98585 s x'' b f x _43496)) = ((term468 _98584 _98585 s x'' b a f x _43496) = (term493 _98584 _98585 s x'' b f x _43496)).
Proof. exact (MK_COMB (@lem3794087 _98584 _98585 s x'' b a f x _43496) (@lem3794088 _98584 _98585 s x'' b f x _43496)). Qed.
Lemma lem3794090 {_98584 _98585 : Type'} (a : _98584) (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : ((term491 _98584 _98585 s x'' b f x _43496 a) = (term492 _98584 _98585 s x'' _43496 f x b)) = ((term468 _98584 _98585 s x'' b a f x _43496) = (term493 _98584 _98585 s x'' b f x _43496)).
Proof. exact (TRANS (@lem3794084 _98584 _98585 a s x'' b f x _43496) (@lem3794089 _98584 _98585 a s x'' b f x _43496)). Qed.
Lemma lem3794091 {_98584 _98585 : Type'} (_43496 : _98584) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : (term468 _98584 _98585 s x'' b a f x _43496) = (term493 _98584 _98585 s x'' b f x _43496).
Proof. exact (EQ_MP (@lem3794090 _98584 _98585 a s x'' b f x _43496) (@lem3794081 _98584 _98585 _43496 x'' s a f x b h1)). Qed.
Lemma lem3794092 {_98584 _98585 : Type'} (_43496 : _98584) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term363 _98584 _98585 s x'' b a f x) (h2 : term400 _98584 _98585 x'' s a f x b) : term493 _98584 _98585 s x'' b f x _43496.
Proof. exact (EQ_MP (@lem3794091 _98584 _98585 _43496 x'' s a f x b h2) (@lem3793123 _98584 _98585 _43496 s x'' b a f x h1)). Qed.
Lemma lem3794093 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term496 _98584 _98585 x'' b f x _43496) = (term496 _98584 _98585 x'' b f x _43496).
Proof. exact (eq_refl (term496 _98584 _98585 x'' b f x _43496)). Qed.
Lemma lem3794094 {_98584 _98585 : Type'} (_43496 : _98584) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : (term497 _98584 _98585 x'' b f x _43496 a) = (term498 _98584 _98585 x'' _43496 f x b).
Proof. exact (MK_COMB (@lem3794093 _98584 _98585 x'' b f x _43496) (@lem3793099 _98584 _98585 x'' s a f x b h1)). Qed.
Lemma lem3794095 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term498 _98584 _98585 x'' _43496 f x b) = (term499 _98584 _98585 x'' b f x _43496).
Proof. exact (eq_refl (term498 _98584 _98585 x'' _43496 f x b)). Qed.
Lemma lem3794096 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) (a : _98584) : (term500 _98584 _98585 x'' b f x _43496 a) = (term500 _98584 _98585 x'' b f x _43496 a).
Proof. exact (eq_refl (term500 _98584 _98585 x'' b f x _43496 a)). Qed.
Lemma lem3794097 {_98584 _98585 : Type'} (a : _98584) (x'' : _98584 -> _98585) (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : ((term497 _98584 _98585 x'' b f x _43496 a) = (term498 _98584 _98585 x'' _43496 f x b)) = ((term497 _98584 _98585 x'' b f x _43496 a) = (term499 _98584 _98585 x'' b f x _43496)).
Proof. exact (MK_COMB (@lem3794096 _98584 _98585 x'' b f x _43496 a) (@lem3794095 _98584 _98585 x'' b f x _43496)). Qed.
Lemma lem3794098 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term497 _98584 _98585 x'' b f x _43496 a) = (term469 _98584 _98585 x'' b a f x _43496).
Proof. exact (eq_refl (term497 _98584 _98585 x'' b f x _43496 a)). Qed.
Lemma lem3794099 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3794100 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (b : _98584) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term500 _98584 _98585 x'' b f x _43496 a) = (term501 _98584 _98585 x'' b a f x _43496).
Proof. exact (MK_COMB (@lem3794099) (@lem3794098 _98584 _98585 x'' b a f x _43496)). Qed.
Lemma lem3794101 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term499 _98584 _98585 x'' b f x _43496) = (term499 _98584 _98585 x'' b f x _43496).
Proof. exact (eq_refl (term499 _98584 _98585 x'' b f x _43496)). Qed.
Lemma lem3794102 {_98584 _98585 : Type'} (a : _98584) (x'' : _98584 -> _98585) (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : ((term497 _98584 _98585 x'' b f x _43496 a) = (term499 _98584 _98585 x'' b f x _43496)) = ((term469 _98584 _98585 x'' b a f x _43496) = (term499 _98584 _98585 x'' b f x _43496)).
Proof. exact (MK_COMB (@lem3794100 _98584 _98585 x'' b a f x _43496) (@lem3794101 _98584 _98585 x'' b f x _43496)). Qed.
Lemma lem3794103 {_98584 _98585 : Type'} (a : _98584) (x'' : _98584 -> _98585) (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : ((term497 _98584 _98585 x'' b f x _43496 a) = (term498 _98584 _98585 x'' _43496 f x b)) = ((term469 _98584 _98585 x'' b a f x _43496) = (term499 _98584 _98585 x'' b f x _43496)).
Proof. exact (TRANS (@lem3794097 _98584 _98585 a x'' b f x _43496) (@lem3794102 _98584 _98585 a x'' b f x _43496)). Qed.
Lemma lem3794104 {_98584 _98585 : Type'} (_43496 : _98584) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : (term469 _98584 _98585 x'' b a f x _43496) = (term499 _98584 _98585 x'' b f x _43496).
Proof. exact (EQ_MP (@lem3794103 _98584 _98585 a x'' b f x _43496) (@lem3794094 _98584 _98585 _43496 x'' s a f x b h1)). Qed.
Lemma lem3794105 {_98584 _98585 : Type'} (_43496 : _98584) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term363 _98584 _98585 s x'' b a f x) (h2 : term400 _98584 _98585 x'' s a f x b) : term499 _98584 _98585 x'' b f x _43496.
Proof. exact (EQ_MP (@lem3794104 _98584 _98585 _43496 x'' s a f x b h2) (@lem3793135 _98584 _98585 _43496 s x'' b a f x h1)). Qed.
Lemma lem3794121 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3794122 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : s x') : term502 _98585 s x'.
Proof. exact (fun h0 : term374 _98585 s x' => @lem3794121 _98585 s x' h1). Qed.
Lemma lem3794124 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3794125 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) : (term502 _98585 s x') = (s x').
Proof. exact (@lem3794124 (s x')). Qed.
Lemma lem3794126 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3794125 _98585 s x') (@lem3794122 _98585 s x' h1)). Qed.
Lemma lem3794129 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3794131 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) : (term374 _98585 s x') = (term504 _98585 s x').
Proof. exact (@lem3794129 (s x')). Qed.
Lemma lem3794134 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') : term504 _98585 s x'.
Proof. exact (EQ_MP (@lem3794131 _98585 s x') (@lem3793274 _98585 s x' h1)). Qed.
Lemma lem3794137 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') (h2 : s x') : False.
Proof. exact (@lem3794134 _98585 s x' h1 (@lem3794126 _98585 s x' h2)). Qed.
Lemma lem3794138 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') (h2 : s x') : term505.
Proof. exact (fun h0 : ~ False => @lem3794137 _98585 s x' h1 h2). Qed.
Lemma lem3794140 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3794141 : term505 = False.
Proof. exact (@lem3794140 False). Qed.
Lemma lem3794142 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3794141) (@lem3794138 _98585 s x' h1 h2)). Qed.
Lemma lem3794158 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : s x.
Proof. exact (proj1 (@lem3792687 _98584 _98585 c s x' a f x b h1)). Qed.
Lemma lem3794159 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : term502 _98585 s x.
Proof. exact (fun h0 : term374 _98585 s x => @lem3794158 _98584 _98585 c s x' a f x b h1). Qed.
Lemma lem3794161 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3794162 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term502 _98585 s x) = (s x).
Proof. exact (@lem3794161 (s x)). Qed.
Lemma lem3794163 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : s x.
Proof. exact (EQ_MP (@lem3794162 _98585 s x) (@lem3794159 _98584 _98585 c s x' a f x b h1)). Qed.
Lemma lem3794166 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3794168 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term374 _98585 s x) = (term504 _98585 s x).
Proof. exact (@lem3794166 (s x)). Qed.
Lemma lem3794171 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (x : _98585) (h1 : term374 _98585 s x') (h2 : x' = x) : term504 _98585 s x.
Proof. exact (EQ_MP (@lem3794168 _98585 s x) (@lem3793496 _98585 s x' x h1 h2)). Qed.
Lemma lem3794174 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) (x' : _98585) (x : _98585) (h1 : term374 _98585 s x') (h2 : term303 _98584 _98585 c s x' a f x b) (h3 : x' = x) : False.
Proof. exact (@lem3794171 _98585 s x' x h1 h3 (@lem3794163 _98584 _98585 c s x' a f x b h2)). Qed.
Lemma lem3794175 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) (x' : _98585) (x : _98585) (h1 : term374 _98585 s x') (h2 : term303 _98584 _98585 c s x' a f x b) (h3 : x' = x) : term505.
Proof. exact (fun h0 : ~ False => @lem3794174 _98584 _98585 c s a f b x' x h1 h2 h3). Qed.
Lemma lem3794177 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3794178 : term505 = False.
Proof. exact (@lem3794177 False). Qed.
Lemma lem3794195 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3794196 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : s x') : term502 _98585 s x'.
Proof. exact (fun h0 : term374 _98585 s x' => @lem3794195 _98585 s x' h1). Qed.
Lemma lem3794198 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3794199 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) : (term502 _98585 s x') = (s x').
Proof. exact (@lem3794198 (s x')). Qed.
Lemma lem3794200 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3794199 _98585 s x') (@lem3794196 _98585 s x' h1)). Qed.
Lemma lem3794206 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3794207 {_98585 : Type'} (x : _98585) (s : _98585 -> Prop) (_43489 : _98585) : (term148 _98585 s _43489 x) = (term506 _98585 x s _43489).
Proof. exact (@lem3794206 (_43489 = x) (term374 _98585 s _43489)). Qed.
Lemma lem3794215 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3794216 {_98585 : Type'} (x : _98585) (s : _98585 -> Prop) (_43489 : _98585) : (term507 _98585 s _43489 x) = (term508 _98585 x s _43489).
Proof. exact (MK_COMB (@lem3794215) (@lem3794207 _98585 x s _43489)). Qed.
Lemma lem3794224 {_98585 : Type'} (x : _98585) (s : _98585 -> Prop) (_43489 : _98585) : (term506 _98585 x s _43489) = (term506 _98585 x s _43489).
Proof. exact (eq_refl (term506 _98585 x s _43489)). Qed.
Lemma lem3794225 {_98585 : Type'} (x : _98585) (s : _98585 -> Prop) (_43489 : _98585) : ((term148 _98585 s _43489 x) = (term506 _98585 x s _43489)) = ((term506 _98585 x s _43489) = (term506 _98585 x s _43489)).
Proof. exact (MK_COMB (@lem3794216 _98585 x s _43489) (@lem3794224 _98585 x s _43489)). Qed.
Lemma lem3794227 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3794228 (x : Prop) : (x = x) = True.
Proof. exact (@lem3794227 Prop x). Qed.
Lemma lem3794229 {_98585 : Type'} (x : _98585) (s : _98585 -> Prop) (_43489 : _98585) : ((term506 _98585 x s _43489) = (term506 _98585 x s _43489)) = True.
Proof. exact (@lem3794228 (term506 _98585 x s _43489)). Qed.
Lemma lem3794230 {_98585 : Type'} (x : _98585) (s : _98585 -> Prop) (_43489 : _98585) : ((term148 _98585 s _43489 x) = (term506 _98585 x s _43489)) = True.
Proof. exact (TRANS (@lem3794225 _98585 x s _43489) (@lem3794229 _98585 x s _43489)). Qed.
Lemma lem3794231 {_98585 : Type'} (x : _98585) (s : _98585 -> Prop) (_43489 : _98585) : True = ((term148 _98585 s _43489 x) = (term506 _98585 x s _43489)).
Proof. exact (SYM (@lem3794230 _98585 x s _43489)). Qed.
Lemma lem3794232 {_98585 : Type'} (x : _98585) (s : _98585 -> Prop) (_43489 : _98585) : (term148 _98585 s _43489 x) = (term506 _98585 x s _43489).
Proof. exact (EQ_MP (@lem3794231 _98585 x s _43489) (@lem0)). Qed.
Lemma lem3794233 {_98584 _98585 : Type'} (_43489 : _98585) (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : term506 _98585 x s _43489.
Proof. exact (EQ_MP (@lem3794232 _98585 x s _43489) (@lem3793621 _98584 _98585 _43489 c s x' a f x b h1)). Qed.
Lemma lem3794235 (b : Prop) (a : Prop) : (a \/ b) = (term509 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3794236 {_98585 : Type'} (s : _98585 -> Prop) (_43489 : _98585) (x : _98585) : (term506 _98585 x s _43489) = (term510 _98585 s _43489 x).
Proof. exact (@lem3794235 (term374 _98585 s _43489) (_43489 = x)). Qed.
Lemma lem3794238 (a : Prop) : (term108 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3794239 {_98585 : Type'} (s : _98585 -> Prop) (_43489 : _98585) : (term511 _98585 s _43489) = (s _43489).
Proof. exact (@lem3794238 (s _43489)). Qed.
Lemma lem3794240 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3794241 {_98585 : Type'} (s : _98585 -> Prop) (_43489 : _98585) : (term512 _98585 s _43489) = (term513 _98585 s _43489).
Proof. exact (MK_COMB (@lem3794240) (@lem3794239 _98585 s _43489)). Qed.
Lemma lem3794242 {_98585 : Type'} (_43489 : _98585) (x : _98585) : (_43489 = x) = (_43489 = x).
Proof. exact (eq_refl (_43489 = x)). Qed.
Lemma lem3794243 {_98585 : Type'} (s : _98585 -> Prop) (_43489 : _98585) (x : _98585) : (term510 _98585 s _43489 x) = (term514 _98585 s _43489 x).
Proof. exact (MK_COMB (@lem3794241 _98585 s _43489) (@lem3794242 _98585 _43489 x)). Qed.
Lemma lem3794244 {_98585 : Type'} (s : _98585 -> Prop) (_43489 : _98585) (x : _98585) : (term506 _98585 x s _43489) = (term514 _98585 s _43489 x).
Proof. exact (TRANS (@lem3794236 _98585 s _43489 x) (@lem3794243 _98585 s _43489 x)). Qed.
Lemma lem3794247 {_98584 _98585 : Type'} (_43489 : _98585) (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : term514 _98585 s _43489 x.
Proof. exact (EQ_MP (@lem3794244 _98585 s _43489 x) (@lem3794233 _98584 _98585 _43489 c s x' a f x b h1)). Qed.
Lemma lem3794248 {_98584 _98585 : Type'} (_43489 : _98585) (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : term514 _98585 s _43489 x.
Proof. exact (@lem3794247 _98584 _98585 _43489 c s x' a f x b h1). Qed.
Lemma lem3794249 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : term514 _98585 s x' x.
Proof. exact (@lem3794248 _98584 _98585 x' c s x' a f x b h1). Qed.
Lemma lem3794252 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : s x') (h2 : term303 _98584 _98585 c s x' a f x b) : x' = x.
Proof. exact (@lem3794249 _98584 _98585 c s x' a f x b h2 (@lem3794200 _98585 s x' h1)). Qed.
Lemma lem3794253 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : s x') (h2 : term303 _98584 _98585 c s x' a f x b) : term515 _98585 x' x.
Proof. exact (fun h0 : term72 _98585 x' x => @lem3794252 _98584 _98585 c s x' a f x b h1 h2). Qed.
Lemma lem3794255 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3794256 {_98585 : Type'} (x' : _98585) (x : _98585) : (term515 _98585 x' x) = (x' = x).
Proof. exact (@lem3794255 (x' = x)). Qed.
Lemma lem3794257 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : s x') (h2 : term303 _98584 _98585 c s x' a f x b) : x' = x.
Proof. exact (EQ_MP (@lem3794256 _98585 x' x) (@lem3794253 _98584 _98585 c s x' a f x b h1 h2)). Qed.
Lemma lem3794260 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3794262 {_98585 : Type'} (x' : _98585) (x : _98585) : (term72 _98585 x' x) = (term516 _98585 x' x).
Proof. exact (@lem3794260 (x' = x)). Qed.
Lemma lem3794265 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) : term516 _98585 x' x.
Proof. exact (EQ_MP (@lem3794262 _98585 x' x) (@lem3793635 _98585 x' x h1)). Qed.
Lemma lem3794268 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term72 _98585 x' x) (h2 : s x') (h3 : term303 _98584 _98585 c s x' a f x b) : False.
Proof. exact (@lem3794265 _98585 x' x h1 (@lem3794257 _98584 _98585 c s x' a f x b h2 h3)). Qed.
Lemma lem3794269 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term72 _98585 x' x) (h2 : s x') (h3 : term303 _98584 _98585 c s x' a f x b) : term505.
Proof. exact (fun h0 : ~ False => @lem3794268 _98584 _98585 c s x' a f x b h1 h2 h3). Qed.
Lemma lem3794271 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3794272 : term505 = False.
Proof. exact (@lem3794271 False). Qed.
Lemma lem3794273 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term72 _98585 x' x) (h2 : s x') (h3 : term303 _98584 _98585 c s x' a f x b) : False.
Proof. exact (EQ_MP (@lem3794272) (@lem3794269 _98584 _98585 c s x' a f x b h1 h2 h3)). Qed.
Lemma lem3794289 {_98585 : Type'} (x : _98585) : x = x.
Proof. exact (@lem21386 _98585 x). Qed.
Lemma lem3794290 {_98585 : Type'} (x : _98585) : x = x.
Proof. exact (@lem3794289 _98585 x). Qed.
Lemma lem3794291 {_98585 : Type'} (x : _98585) : term517 _98585 x.
Proof. exact (fun h0 : term477 _98585 x => @lem3794290 _98585 x). Qed.
Lemma lem3794293 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3794294 {_98585 : Type'} (x : _98585) : (term517 _98585 x) = (x = x).
Proof. exact (@lem3794293 (x = x)). Qed.
Lemma lem3794295 {_98585 : Type'} (x : _98585) : x = x.
Proof. exact (EQ_MP (@lem3794294 _98585 x) (@lem3794291 _98585 x)). Qed.
Lemma lem3794298 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3794300 {_98585 : Type'} (x : _98585) : (term477 _98585 x) = (term518 _98585 x).
Proof. exact (@lem3794298 (x = x)). Qed.
Lemma lem3794303 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) (h2 : x' = x) : term518 _98585 x.
Proof. exact (EQ_MP (@lem3794300 _98585 x) (@lem3793857 _98585 x' x h1 h2)). Qed.
Lemma lem3794306 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) (h2 : x' = x) : False.
Proof. exact (@lem3794303 _98585 x' x h1 h2 (@lem3794295 _98585 x)). Qed.
Lemma lem3794307 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) (h2 : x' = x) : term505.
Proof. exact (fun h0 : ~ False => @lem3794306 _98585 x' x h1 h2). Qed.
Lemma lem3794309 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3794310 : term505 = False.
Proof. exact (@lem3794309 False). Qed.
Lemma lem3794344 {_98584 : Type'} (x : _98584) : x = x.
Proof. exact (@lem21386 _98584 x). Qed.
Lemma lem3794345 {_98584 : Type'} (x : _98584) : x = x.
Proof. exact (@lem3794344 _98584 x). Qed.
Lemma lem3794346 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (f x b) = (f x b).
Proof. exact (@lem3794345 _98584 (f x b)). Qed.
Lemma lem3794347 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : term519 _98584 _98585 f x b.
Proof. exact (fun h0 : term487 _98584 _98585 f x b => @lem3794346 _98584 _98585 f x b). Qed.
Lemma lem3794349 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3794350 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term519 _98584 _98585 f x b) = ((f x b) = (f x b)).
Proof. exact (@lem3794349 ((f x b) = (f x b))). Qed.
Lemma lem3794351 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (f x b) = (f x b).
Proof. exact (EQ_MP (@lem3794350 _98584 _98585 f x b) (@lem3794347 _98584 _98585 f x b)). Qed.
Lemma lem3794354 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3794356 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term487 _98584 _98585 f x b) = (term520 _98584 _98585 f x b).
Proof. exact (@lem3794354 ((f x b) = (f x b))). Qed.
Lemma lem3794359 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term168 _98584 _98585 a f x b) (h2 : term303 _98584 _98585 c s x' a f x b) : term520 _98584 _98585 f x b.
Proof. exact (EQ_MP (@lem3794356 _98584 _98585 f x b) (@lem3793981 _98584 _98585 c s x' a f x b h1 h2)). Qed.
Lemma lem3794362 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term168 _98584 _98585 a f x b) (h2 : term303 _98584 _98585 c s x' a f x b) : False.
Proof. exact (@lem3794359 _98584 _98585 c s x' a f x b h1 h2 (@lem3794351 _98584 _98585 f x b)). Qed.
Lemma lem3794363 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term168 _98584 _98585 a f x b) (h2 : term303 _98584 _98585 c s x' a f x b) : term505.
Proof. exact (fun h0 : ~ False => @lem3794362 _98584 _98585 c s x' a f x b h1 h2). Qed.
Lemma lem3794365 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3794366 : term505 = False.
Proof. exact (@lem3794365 False). Qed.
Lemma lem3794383 {_98585 : Type'} (x : _98585) : x = x.
Proof. exact (@lem21386 _98585 x). Qed.
Lemma lem3794384 {_98585 : Type'} (x : _98585) : x = x.
Proof. exact (@lem3794383 _98585 x). Qed.
Lemma lem3794385 {_98585 : Type'} (x : _98585) : term517 _98585 x.
Proof. exact (fun h0 : term477 _98585 x => @lem3794384 _98585 x). Qed.
Lemma lem3794387 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3794388 {_98585 : Type'} (x : _98585) : (term517 _98585 x) = (x = x).
Proof. exact (@lem3794387 (x = x)). Qed.
Lemma lem3794389 {_98585 : Type'} (x : _98585) : x = x.
Proof. exact (EQ_MP (@lem3794388 _98585 x) (@lem3794385 _98585 x)). Qed.
Lemma lem3794391 (b : Prop) (a : Prop) : (a \/ b) = (term509 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3794392 {_98585 : Type'} (x : _98585) (s : _98585 -> Prop) (_43492 : _98585) : (term227 _98585 s _43492 x) = (term521 _98585 x s _43492).
Proof. exact (@lem3794391 (term72 _98585 _43492 x) (s _43492)). Qed.
Lemma lem3794394 (a : Prop) : (term108 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3794395 {_98585 : Type'} (_43492 : _98585) (x : _98585) : (term145 _98585 _43492 x) = (_43492 = x).
Proof. exact (@lem3794394 (_43492 = x)). Qed.
Lemma lem3794396 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3794397 {_98585 : Type'} (_43492 : _98585) (x : _98585) : (term522 _98585 _43492 x) = (term523 _98585 _43492 x).
Proof. exact (MK_COMB (@lem3794396) (@lem3794395 _98585 _43492 x)). Qed.
Lemma lem3794398 {_98585 : Type'} (s : _98585 -> Prop) (_43492 : _98585) : (s _43492) = (s _43492).
Proof. exact (eq_refl (s _43492)). Qed.
Lemma lem3794399 {_98585 : Type'} (x : _98585) (s : _98585 -> Prop) (_43492 : _98585) : (term521 _98585 x s _43492) = (term524 _98585 x s _43492).
Proof. exact (MK_COMB (@lem3794397 _98585 _43492 x) (@lem3794398 _98585 s _43492)). Qed.
Lemma lem3794400 {_98585 : Type'} (x : _98585) (s : _98585 -> Prop) (_43492 : _98585) : (term227 _98585 s _43492 x) = (term524 _98585 x s _43492).
Proof. exact (TRANS (@lem3794392 _98585 x s _43492) (@lem3794399 _98585 x s _43492)). Qed.
Lemma lem3794403 {_98584 _98585 : Type'} (_43492 : _98585) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : term524 _98585 x s _43492.
Proof. exact (EQ_MP (@lem3794400 _98585 x s _43492) (@lem3794009 _98584 _98585 _43492 x'' s a f x b h1)). Qed.
Lemma lem3794404 {_98584 _98585 : Type'} (_43492 : _98585) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : term524 _98585 x s _43492.
Proof. exact (@lem3794403 _98584 _98585 _43492 x'' s a f x b h1). Qed.
Lemma lem3794405 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : term525 _98585 s x.
Proof. exact (@lem3794404 _98584 _98585 x x'' s a f x b h1). Qed.
Lemma lem3794408 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : s x.
Proof. exact (@lem3794405 _98584 _98585 x'' s a f x b h1 (@lem3794389 _98585 x)). Qed.
Lemma lem3794409 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : term502 _98585 s x.
Proof. exact (fun h0 : term374 _98585 s x => @lem3794408 _98584 _98585 x'' s a f x b h1). Qed.
Lemma lem3794411 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3794412 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term502 _98585 s x) = (s x).
Proof. exact (@lem3794411 (s x)). Qed.
Lemma lem3794413 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : s x.
Proof. exact (EQ_MP (@lem3794412 _98585 s x) (@lem3794409 _98584 _98585 x'' s a f x b h1)). Qed.
Lemma lem3794416 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3794418 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) : (term374 _98585 s x) = (term504 _98585 s x).
Proof. exact (@lem3794416 (s x)). Qed.
Lemma lem3794421 {_98585 : Type'} (s : _98585 -> Prop) (x : _98585) (h1 : term374 _98585 s x) : term504 _98585 s x.
Proof. exact (EQ_MP (@lem3794418 _98585 s x) (@lem3794037 _98585 s x h1)). Qed.
Lemma lem3794424 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term374 _98585 s x) (h2 : term400 _98584 _98585 x'' s a f x b) : False.
Proof. exact (@lem3794421 _98585 s x h1 (@lem3794413 _98584 _98585 x'' s a f x b h2)). Qed.
Lemma lem3794425 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term374 _98585 s x) (h2 : term400 _98584 _98585 x'' s a f x b) : term505.
Proof. exact (fun h0 : ~ False => @lem3794424 _98584 _98585 x'' s a f x b h1 h2). Qed.
Lemma lem3794427 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3794428 : term505 = False.
Proof. exact (@lem3794427 False). Qed.
Lemma lem3794429 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term374 _98585 s x) (h2 : term400 _98584 _98585 x'' s a f x b) : False.
Proof. exact (EQ_MP (@lem3794428) (@lem3794425 _98584 _98585 x'' s a f x b h1 h2)). Qed.
Lemma lem3794470 {_98584 : Type'} (x : _98584) : x = x.
Proof. exact (@lem21386 _98584 x). Qed.
Lemma lem3794471 {_98584 : Type'} (x : _98584) : x = x.
Proof. exact (@lem3794470 _98584 x). Qed.
Lemma lem3794472 {_98584 : Type'} (b : _98584) : b = b.
Proof. exact (@lem3794471 _98584 b). Qed.
Lemma lem3794473 {_98584 : Type'} (b : _98584) : term517 _98584 b.
Proof. exact (fun h0 : term477 _98584 b => @lem3794472 _98584 b). Qed.
Lemma lem3794475 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3794476 {_98584 : Type'} (b : _98584) : (term517 _98584 b) = (b = b).
Proof. exact (@lem3794475 (b = b)). Qed.
Lemma lem3794477 {_98584 : Type'} (b : _98584) : b = b.
Proof. exact (EQ_MP (@lem3794476 _98584 b) (@lem3794473 _98584 b)). Qed.
Lemma lem3794479 {_98584 : Type'} (x : _98584) : x = x.
Proof. exact (@lem21386 _98584 x). Qed.
Lemma lem3794480 {_98584 : Type'} (x : _98584) : x = x.
Proof. exact (@lem3794479 _98584 x). Qed.
Lemma lem3794481 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (f x b) = (f x b).
Proof. exact (@lem3794480 _98584 (f x b)). Qed.
Lemma lem3794482 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : term519 _98584 _98585 f x b.
Proof. exact (fun h0 : term487 _98584 _98585 f x b => @lem3794481 _98584 _98585 f x b). Qed.
Lemma lem3794484 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3794485 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term519 _98584 _98585 f x b) = ((f x b) = (f x b)).
Proof. exact (@lem3794484 ((f x b) = (f x b))). Qed.
Lemma lem3794486 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (f x b) = (f x b).
Proof. exact (EQ_MP (@lem3794485 _98584 _98585 f x b) (@lem3794482 _98584 _98585 f x b)). Qed.
Lemma lem3794488 (b : Prop) (a : Prop) : (a \/ b) = (term509 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3794489 {_98584 _98585 : Type'} (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (s : _98585 -> Prop) (x'' : _98584 -> _98585) (_43496 : _98584) : (term493 _98584 _98585 s x'' b f x _43496) = (term526 _98584 _98585 b f x s x'' _43496).
Proof. exact (@lem3794488 (term527 _98584 _98585 b f x _43496) (term455 _98584 _98585 s x'' _43496)). Qed.
Lemma lem3794491 (a : Prop) (b : Prop) : (term528 a b) = (term529 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3794492 {_98584 _98585 : Type'} (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term530 _98584 _98585 b f x _43496) = (term531 _98584 _98585 b f x _43496).
Proof. exact (@lem3794491 (term72 _98584 _43496 b) (term532 _98584 _98585 b f x _43496)). Qed.
Lemma lem3794494 (a : Prop) : (term108 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3794495 {_98584 : Type'} (_43496 : _98584) (b : _98584) : (term145 _98584 _43496 b) = (_43496 = b).
Proof. exact (@lem3794494 (_43496 = b)). Qed.
Lemma lem3794496 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3794497 {_98584 : Type'} (_43496 : _98584) (b : _98584) : (term533 _98584 _43496 b) = (term534 _98584 _43496 b).
Proof. exact (MK_COMB (@lem3794496) (@lem3794495 _98584 _43496 b)). Qed.
Lemma lem3794499 (a : Prop) : (term108 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3794500 {_98584 _98585 : Type'} (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term535 _98584 _98585 b f x _43496) = ((f x b) = (f x _43496)).
Proof. exact (@lem3794499 ((f x b) = (f x _43496))). Qed.
Lemma lem3794501 {_98584 _98585 : Type'} (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term531 _98584 _98585 b f x _43496) = (term536 _98584 _98585 b f x _43496).
Proof. exact (MK_COMB (@lem3794497 _98584 _43496 b) (@lem3794500 _98584 _98585 b f x _43496)). Qed.
Lemma lem3794502 {_98584 _98585 : Type'} (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term530 _98584 _98585 b f x _43496) = (term536 _98584 _98585 b f x _43496).
Proof. exact (TRANS (@lem3794492 _98584 _98585 b f x _43496) (@lem3794501 _98584 _98585 b f x _43496)). Qed.
Lemma lem3794503 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3794504 {_98584 _98585 : Type'} (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term537 _98584 _98585 b f x _43496) = (term538 _98584 _98585 b f x _43496).
Proof. exact (MK_COMB (@lem3794503) (@lem3794502 _98584 _98585 b f x _43496)). Qed.
Lemma lem3794505 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (_43496 : _98584) : (term455 _98584 _98585 s x'' _43496) = (term455 _98584 _98585 s x'' _43496).
Proof. exact (eq_refl (term455 _98584 _98585 s x'' _43496)). Qed.
Lemma lem3794506 {_98584 _98585 : Type'} (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (s : _98585 -> Prop) (x'' : _98584 -> _98585) (_43496 : _98584) : (term526 _98584 _98585 b f x s x'' _43496) = (term539 _98584 _98585 b f x s x'' _43496).
Proof. exact (MK_COMB (@lem3794504 _98584 _98585 b f x _43496) (@lem3794505 _98584 _98585 s x'' _43496)). Qed.
Lemma lem3794507 {_98584 _98585 : Type'} (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (s : _98585 -> Prop) (x'' : _98584 -> _98585) (_43496 : _98584) : (term493 _98584 _98585 s x'' b f x _43496) = (term539 _98584 _98585 b f x s x'' _43496).
Proof. exact (TRANS (@lem3794489 _98584 _98585 b f x s x'' _43496) (@lem3794506 _98584 _98585 b f x s x'' _43496)). Qed.
Lemma lem3794509 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : term540 _98584 _98585 f x b.
Proof. exact (conj (@lem3794477 _98584 b) (@lem3794486 _98584 _98585 f x b)). Qed.
Lemma lem3794511 {_98584 _98585 : Type'} (_43496 : _98584) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term363 _98584 _98585 s x'' b a f x) (h2 : term400 _98584 _98585 x'' s a f x b) : term539 _98584 _98585 b f x s x'' _43496.
Proof. exact (EQ_MP (@lem3794507 _98584 _98585 b f x s x'' _43496) (@lem3794092 _98584 _98585 _43496 x'' s a f x b h1 h2)). Qed.
Lemma lem3794512 {_98584 _98585 : Type'} (_43496 : _98584) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term363 _98584 _98585 s x'' b a f x) (h2 : term400 _98584 _98585 x'' s a f x b) : term539 _98584 _98585 b f x s x'' _43496.
Proof. exact (@lem3794511 _98584 _98585 _43496 x'' s a f x b h1 h2). Qed.
Lemma lem3794513 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term363 _98584 _98585 s x'' b a f x) (h2 : term400 _98584 _98585 x'' s a f x b) : term541 _98584 _98585 f x s x'' b.
Proof. exact (@lem3794512 _98584 _98585 b x'' s a f x b h1 h2). Qed.
Lemma lem3794516 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term363 _98584 _98585 s x'' b a f x) (h2 : term400 _98584 _98585 x'' s a f x b) : term455 _98584 _98585 s x'' b.
Proof. exact (@lem3794513 _98584 _98585 x'' s a f x b h1 h2 (@lem3794509 _98584 _98585 f x b)). Qed.
Lemma lem3794517 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term363 _98584 _98585 s x'' b a f x) (h2 : term400 _98584 _98585 x'' s a f x b) : term542 _98584 _98585 s x'' b.
Proof. exact (fun h0 : term543 _98584 _98585 s x'' b => @lem3794516 _98584 _98585 x'' s a f x b h1 h2). Qed.
Lemma lem3794519 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3794520 {_98584 _98585 : Type'} (s : _98585 -> Prop) (x'' : _98584 -> _98585) (b : _98584) : (term542 _98584 _98585 s x'' b) = (term455 _98584 _98585 s x'' b).
Proof. exact (@lem3794519 (term455 _98584 _98585 s x'' b)). Qed.
Lemma lem3794521 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term363 _98584 _98585 s x'' b a f x) (h2 : term400 _98584 _98585 x'' s a f x b) : term455 _98584 _98585 s x'' b.
Proof. exact (EQ_MP (@lem3794520 _98584 _98585 s x'' b) (@lem3794517 _98584 _98585 x'' s a f x b h1 h2)). Qed.
Lemma lem3794527 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3794528 {_98585 : Type'} (x : _98585) (s : _98585 -> Prop) (_43495 : _98585) : (term148 _98585 s _43495 x) = (term506 _98585 x s _43495).
Proof. exact (@lem3794527 (_43495 = x) (term374 _98585 s _43495)). Qed.
Lemma lem3794536 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3794537 {_98585 : Type'} (x : _98585) (s : _98585 -> Prop) (_43495 : _98585) : (term507 _98585 s _43495 x) = (term508 _98585 x s _43495).
Proof. exact (MK_COMB (@lem3794536) (@lem3794528 _98585 x s _43495)). Qed.
Lemma lem3794545 {_98585 : Type'} (x : _98585) (s : _98585 -> Prop) (_43495 : _98585) : (term506 _98585 x s _43495) = (term506 _98585 x s _43495).
Proof. exact (eq_refl (term506 _98585 x s _43495)). Qed.
Lemma lem3794546 {_98585 : Type'} (x : _98585) (s : _98585 -> Prop) (_43495 : _98585) : ((term148 _98585 s _43495 x) = (term506 _98585 x s _43495)) = ((term506 _98585 x s _43495) = (term506 _98585 x s _43495)).
Proof. exact (MK_COMB (@lem3794537 _98585 x s _43495) (@lem3794545 _98585 x s _43495)). Qed.
Lemma lem3794548 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3794549 (x : Prop) : (x = x) = True.
Proof. exact (@lem3794548 Prop x). Qed.
Lemma lem3794550 {_98585 : Type'} (x : _98585) (s : _98585 -> Prop) (_43495 : _98585) : ((term506 _98585 x s _43495) = (term506 _98585 x s _43495)) = True.
Proof. exact (@lem3794549 (term506 _98585 x s _43495)). Qed.
Lemma lem3794551 {_98585 : Type'} (x : _98585) (s : _98585 -> Prop) (_43495 : _98585) : ((term148 _98585 s _43495 x) = (term506 _98585 x s _43495)) = True.
Proof. exact (TRANS (@lem3794546 _98585 x s _43495) (@lem3794550 _98585 x s _43495)). Qed.
Lemma lem3794552 {_98585 : Type'} (x : _98585) (s : _98585 -> Prop) (_43495 : _98585) : True = ((term148 _98585 s _43495 x) = (term506 _98585 x s _43495)).
Proof. exact (SYM (@lem3794551 _98585 x s _43495)). Qed.
Lemma lem3794553 {_98585 : Type'} (x : _98585) (s : _98585 -> Prop) (_43495 : _98585) : (term148 _98585 s _43495 x) = (term506 _98585 x s _43495).
Proof. exact (EQ_MP (@lem3794552 _98585 x s _43495) (@lem0)). Qed.
Lemma lem3794554 {_98584 _98585 : Type'} (_43495 : _98585) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : term506 _98585 x s _43495.
Proof. exact (EQ_MP (@lem3794553 _98585 x s _43495) (@lem3794079 _98584 _98585 _43495 x'' s a f x b h1)). Qed.
Lemma lem3794556 (b : Prop) (a : Prop) : (a \/ b) = (term509 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3794557 {_98585 : Type'} (s : _98585 -> Prop) (_43495 : _98585) (x : _98585) : (term506 _98585 x s _43495) = (term510 _98585 s _43495 x).
Proof. exact (@lem3794556 (term374 _98585 s _43495) (_43495 = x)). Qed.
Lemma lem3794559 (a : Prop) : (term108 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3794560 {_98585 : Type'} (s : _98585 -> Prop) (_43495 : _98585) : (term511 _98585 s _43495) = (s _43495).
Proof. exact (@lem3794559 (s _43495)). Qed.
Lemma lem3794561 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3794562 {_98585 : Type'} (s : _98585 -> Prop) (_43495 : _98585) : (term512 _98585 s _43495) = (term513 _98585 s _43495).
Proof. exact (MK_COMB (@lem3794561) (@lem3794560 _98585 s _43495)). Qed.
Lemma lem3794563 {_98585 : Type'} (_43495 : _98585) (x : _98585) : (_43495 = x) = (_43495 = x).
Proof. exact (eq_refl (_43495 = x)). Qed.
Lemma lem3794564 {_98585 : Type'} (s : _98585 -> Prop) (_43495 : _98585) (x : _98585) : (term510 _98585 s _43495 x) = (term514 _98585 s _43495 x).
Proof. exact (MK_COMB (@lem3794562 _98585 s _43495) (@lem3794563 _98585 _43495 x)). Qed.
Lemma lem3794565 {_98585 : Type'} (s : _98585 -> Prop) (_43495 : _98585) (x : _98585) : (term506 _98585 x s _43495) = (term514 _98585 s _43495 x).
Proof. exact (TRANS (@lem3794557 _98585 s _43495 x) (@lem3794564 _98585 s _43495 x)). Qed.
Lemma lem3794568 {_98584 _98585 : Type'} (_43495 : _98585) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : term514 _98585 s _43495 x.
Proof. exact (EQ_MP (@lem3794565 _98585 s _43495 x) (@lem3794554 _98584 _98585 _43495 x'' s a f x b h1)). Qed.
Lemma lem3794569 {_98584 _98585 : Type'} (_43495 : _98585) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : term514 _98585 s _43495 x.
Proof. exact (@lem3794568 _98584 _98585 _43495 x'' s a f x b h1). Qed.
Lemma lem3794570 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : term544 _98584 _98585 s x'' b x.
Proof. exact (@lem3794569 _98584 _98585 (x'' b) x'' s a f x b h1). Qed.
Lemma lem3794573 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term363 _98584 _98585 s x'' b a f x) (h2 : term400 _98584 _98585 x'' s a f x b) : (x'' b) = x.
Proof. exact (@lem3794570 _98584 _98585 x'' s a f x b h2 (@lem3794521 _98584 _98585 x'' s a f x b h1 h2)). Qed.
Lemma lem3794574 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term363 _98584 _98585 s x'' b a f x) (h2 : term400 _98584 _98585 x'' s a f x b) : term545 _98584 _98585 x'' b x.
Proof. exact (fun h0 : term456 _98584 _98585 x'' b x => @lem3794573 _98584 _98585 x'' s a f x b h1 h2). Qed.
Lemma lem3794576 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3794577 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (b : _98584) (x : _98585) : (term545 _98584 _98585 x'' b x) = ((x'' b) = x).
Proof. exact (@lem3794576 ((x'' b) = x)). Qed.
Lemma lem3794578 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term363 _98584 _98585 s x'' b a f x) (h2 : term400 _98584 _98585 x'' s a f x b) : (x'' b) = x.
Proof. exact (EQ_MP (@lem3794577 _98584 _98585 x'' b x) (@lem3794574 _98584 _98585 x'' s a f x b h1 h2)). Qed.
Lemma lem3794580 {_98584 : Type'} (x : _98584) : x = x.
Proof. exact (@lem21386 _98584 x). Qed.
Lemma lem3794581 {_98584 : Type'} (x : _98584) : x = x.
Proof. exact (@lem3794580 _98584 x). Qed.
Lemma lem3794582 {_98584 : Type'} (b : _98584) : b = b.
Proof. exact (@lem3794581 _98584 b). Qed.
Lemma lem3794583 {_98584 : Type'} (b : _98584) : term517 _98584 b.
Proof. exact (fun h0 : term477 _98584 b => @lem3794582 _98584 b). Qed.
Lemma lem3794585 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3794586 {_98584 : Type'} (b : _98584) : (term517 _98584 b) = (b = b).
Proof. exact (@lem3794585 (b = b)). Qed.
Lemma lem3794587 {_98584 : Type'} (b : _98584) : b = b.
Proof. exact (EQ_MP (@lem3794586 _98584 b) (@lem3794583 _98584 b)). Qed.
Lemma lem3794589 {_98584 : Type'} (x : _98584) : x = x.
Proof. exact (@lem21386 _98584 x). Qed.
Lemma lem3794590 {_98584 : Type'} (x : _98584) : x = x.
Proof. exact (@lem3794589 _98584 x). Qed.
Lemma lem3794591 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (f x b) = (f x b).
Proof. exact (@lem3794590 _98584 (f x b)). Qed.
Lemma lem3794592 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : term519 _98584 _98585 f x b.
Proof. exact (fun h0 : term487 _98584 _98585 f x b => @lem3794591 _98584 _98585 f x b). Qed.
Lemma lem3794594 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3794595 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term519 _98584 _98585 f x b) = ((f x b) = (f x b)).
Proof. exact (@lem3794594 ((f x b) = (f x b))). Qed.
Lemma lem3794596 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (f x b) = (f x b).
Proof. exact (EQ_MP (@lem3794595 _98584 _98585 f x b) (@lem3794592 _98584 _98585 f x b)). Qed.
Lemma lem3794598 (a : Prop) (b : Prop) : (term546 a b) = (term547 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3794599 {_98584 _98585 : Type'} (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term527 _98584 _98585 b f x _43496) = (term548 _98584 _98585 b f x _43496).
Proof. exact (@lem3794598 (_43496 = b) ((f x b) = (f x _43496))). Qed.
Lemma lem3794600 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (_43496 : _98584) (x : _98585) : (term549 _98584 _98585 x'' _43496 x) = (term549 _98584 _98585 x'' _43496 x).
Proof. exact (eq_refl (term549 _98584 _98585 x'' _43496 x)). Qed.
Lemma lem3794601 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term499 _98584 _98585 x'' b f x _43496) = (term550 _98584 _98585 x'' b f x _43496).
Proof. exact (MK_COMB (@lem3794600 _98584 _98585 x'' _43496 x) (@lem3794599 _98584 _98585 b f x _43496)). Qed.
Lemma lem3794603 (a : Prop) (b : Prop) : (term546 a b) = (term547 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3794604 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term550 _98584 _98585 x'' b f x _43496) = (term551 _98584 _98585 x'' b f x _43496).
Proof. exact (@lem3794603 ((x'' _43496) = x) (term536 _98584 _98585 b f x _43496)). Qed.
Lemma lem3794605 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term499 _98584 _98585 x'' b f x _43496) = (term551 _98584 _98585 x'' b f x _43496).
Proof. exact (TRANS (@lem3794601 _98584 _98585 x'' b f x _43496) (@lem3794604 _98584 _98585 x'' b f x _43496)). Qed.
Lemma lem3794607 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3794608 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term551 _98584 _98585 x'' b f x _43496) = (term552 _98584 _98585 x'' b f x _43496).
Proof. exact (@lem3794607 (term553 _98584 _98585 x'' b f x _43496)). Qed.
Lemma lem3794609 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (b : _98584) (f : type1467 _98584 _98585) (x : _98585) (_43496 : _98584) : (term499 _98584 _98585 x'' b f x _43496) = (term552 _98584 _98585 x'' b f x _43496).
Proof. exact (TRANS (@lem3794605 _98584 _98585 x'' b f x _43496) (@lem3794608 _98584 _98585 x'' b f x _43496)). Qed.
Lemma lem3794611 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : term540 _98584 _98585 f x b.
Proof. exact (conj (@lem3794587 _98584 b) (@lem3794596 _98584 _98585 f x b)). Qed.
Lemma lem3794612 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term363 _98584 _98585 s x'' b a f x) (h2 : term400 _98584 _98585 x'' s a f x b) : term554 _98584 _98585 x'' f x b.
Proof. exact (conj (@lem3794578 _98584 _98585 x'' s a f x b h1 h2) (@lem3794611 _98584 _98585 f x b)). Qed.
Lemma lem3794614 {_98584 _98585 : Type'} (_43496 : _98584) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term363 _98584 _98585 s x'' b a f x) (h2 : term400 _98584 _98585 x'' s a f x b) : term552 _98584 _98585 x'' b f x _43496.
Proof. exact (EQ_MP (@lem3794609 _98584 _98585 x'' b f x _43496) (@lem3794105 _98584 _98585 _43496 x'' s a f x b h1 h2)). Qed.
Lemma lem3794615 {_98584 _98585 : Type'} (_43496 : _98584) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term363 _98584 _98585 s x'' b a f x) (h2 : term400 _98584 _98585 x'' s a f x b) : term552 _98584 _98585 x'' b f x _43496.
Proof. exact (@lem3794614 _98584 _98585 _43496 x'' s a f x b h1 h2). Qed.
Lemma lem3794616 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term363 _98584 _98585 s x'' b a f x) (h2 : term400 _98584 _98585 x'' s a f x b) : term555 _98584 _98585 x'' f x b.
Proof. exact (@lem3794615 _98584 _98585 b x'' s a f x b h1 h2). Qed.
Lemma lem3794619 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term363 _98584 _98585 s x'' b a f x) (h2 : term400 _98584 _98585 x'' s a f x b) : False.
Proof. exact (@lem3794616 _98584 _98585 x'' s a f x b h1 h2 (@lem3794612 _98584 _98585 x'' s a f x b h1 h2)). Qed.
Lemma lem3794620 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term363 _98584 _98585 s x'' b a f x) (h2 : term400 _98584 _98585 x'' s a f x b) : term505.
Proof. exact (fun h0 : ~ False => @lem3794619 _98584 _98585 x'' s a f x b h1 h2). Qed.
Lemma lem3794622 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3794623 : term505 = False.
Proof. exact (@lem3794622 False). Qed.
Lemma lem3794625 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term363 _98584 _98585 s x'' b a f x) (h2 : term400 _98584 _98585 x'' s a f x b) : False.
Proof. exact (EQ_MP (@lem3794623) (@lem3794620 _98584 _98585 x'' s a f x b h1 h2)). Qed.
Lemma lem3794626 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term374 _98585 s x) (h2 : term400 _98584 _98585 x'' s a f x b) : (term374 _98585 s x) = False.
Proof. exact (prop_ext (fun h3 : term374 _98585 s x => @lem3794429 _98584 _98585 x'' s a f x b h1 h2) (fun h3 : False => @lem3794037 _98585 s x h1)). Qed.
Lemma lem3794628 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term374 _98585 s x) (h2 : term400 _98584 _98585 x'' s a f x b) : False.
Proof. exact (EQ_MP (@lem3794626 _98584 _98585 x'' s a f x b h1 h2) (@lem3794037 _98585 s x h1)). Qed.
Lemma lem3794629 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term168 _98584 _98585 a f x b) (h2 : term303 _98584 _98585 c s x' a f x b) : False.
Proof. exact (EQ_MP (@lem3794366) (@lem3794363 _98584 _98585 c s x' a f x b h1 h2)). Qed.
Lemma lem3794630 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term168 _98584 _98585 a f x b) (h2 : term303 _98584 _98585 c s x' a f x b) : (term168 _98584 _98585 a f x b) = False.
Proof. exact (prop_ext (fun h3 : term168 _98584 _98585 a f x b => @lem3794629 _98584 _98585 c s x' a f x b h1 h2) (fun h3 : False => @lem3793926 _98584 _98585 a f x b h1)). Qed.
Lemma lem3794632 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term168 _98584 _98585 a f x b) (h2 : term303 _98584 _98585 c s x' a f x b) : False.
Proof. exact (EQ_MP (@lem3794630 _98584 _98585 c s x' a f x b h1 h2) (@lem3793926 _98584 _98585 a f x b h1)). Qed.
Lemma lem3794635 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3794310) (@lem3794307 _98585 x' x h1 h2)). Qed.
Lemma lem3794636 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term72 _98585 x' x) (h2 : s x') (h3 : term303 _98584 _98585 c s x' a f x b) : (s x') = False.
Proof. exact (prop_ext (fun h4 : s x' => @lem3794273 _98584 _98585 c s x' a f x b h1 h2 h3) (fun h4 : False => @lem3793649 _98585 s x' h2)). Qed.
Lemma lem3794637 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term72 _98585 x' x) (h2 : s x') (h3 : term303 _98584 _98585 c s x' a f x b) : False.
Proof. exact (EQ_MP (@lem3794636 _98584 _98585 c s x' a f x b h1 h2 h3) (@lem3793649 _98585 s x' h2)). Qed.
Lemma lem3794638 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term72 _98585 x' x) (h2 : s x') (h3 : term303 _98584 _98585 c s x' a f x b) : (term72 _98585 x' x) = False.
Proof. exact (prop_ext (fun h4 : term72 _98585 x' x => @lem3794637 _98584 _98585 c s x' a f x b h1 h2 h3) (fun h4 : False => @lem3793635 _98585 x' x h1)). Qed.
Lemma lem3794640 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term72 _98585 x' x) (h2 : s x') (h3 : term303 _98584 _98585 c s x' a f x b) : False.
Proof. exact (EQ_MP (@lem3794638 _98584 _98585 c s x' a f x b h1 h2 h3) (@lem3793635 _98585 x' x h1)). Qed.
Lemma lem3794641 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term72 _98585 x' x) (h2 : s x') (h3 : term303 _98584 _98585 c s x' a f x b) : (s x') = False.
Proof. exact (prop_ext (fun h4 : s x' => @lem3794640 _98584 _98585 c s x' a f x b h1 h2 h3) (fun h4 : False => @lem3793579 _98585 s x' h2)). Qed.
Lemma lem3794642 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term72 _98585 x' x) (h2 : s x') (h3 : term303 _98584 _98585 c s x' a f x b) : False.
Proof. exact (EQ_MP (@lem3794641 _98584 _98585 c s x' a f x b h1 h2 h3) (@lem3793579 _98585 s x' h2)). Qed.
Lemma lem3794643 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term72 _98585 x' x) (h2 : s x') (h3 : term303 _98584 _98585 c s x' a f x b) : (term72 _98585 x' x) = False.
Proof. exact (prop_ext (fun h4 : term72 _98585 x' x => @lem3794642 _98584 _98585 c s x' a f x b h1 h2 h3) (fun h4 : False => @lem3793565 _98585 x' x h1)). Qed.
Lemma lem3794645 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term72 _98585 x' x) (h2 : s x') (h3 : term303 _98584 _98585 c s x' a f x b) : False.
Proof. exact (EQ_MP (@lem3794643 _98584 _98585 c s x' a f x b h1 h2 h3) (@lem3793565 _98585 x' x h1)). Qed.
Lemma lem3794648 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) (x' : _98585) (x : _98585) (h1 : term374 _98585 s x') (h2 : term303 _98584 _98585 c s x' a f x b) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3794178) (@lem3794175 _98584 _98585 c s a f b x' x h1 h2 h3)). Qed.
Lemma lem3794649 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3794142 _98585 s x' h1 h2) (fun h3 : False => @lem3793288 _98585 s x' h2)). Qed.
Lemma lem3794650 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3794649 _98585 s x' h1 h2) (@lem3793288 _98585 s x' h2)). Qed.
Lemma lem3794651 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') (h2 : s x') : (term374 _98585 s x') = False.
Proof. exact (prop_ext (fun h3 : term374 _98585 s x' => @lem3794650 _98585 s x' h1 h2) (fun h3 : False => @lem3793274 _98585 s x' h1)). Qed.
Lemma lem3794653 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3794651 _98585 s x' h1 h2) (@lem3793274 _98585 s x' h1)). Qed.
Lemma lem3794654 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3794653 _98585 s x' h1 h2) (fun h3 : False => @lem3793218 _98585 s x' h2)). Qed.
Lemma lem3794655 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3794654 _98585 s x' h1 h2) (@lem3793218 _98585 s x' h2)). Qed.
Lemma lem3794656 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') (h2 : s x') : (term374 _98585 s x') = False.
Proof. exact (prop_ext (fun h3 : term374 _98585 s x' => @lem3794655 _98585 s x' h1 h2) (fun h3 : False => @lem3793204 _98585 s x' h1)). Qed.
Lemma lem3794658 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3794656 _98585 s x' h1 h2) (@lem3793204 _98585 s x' h1)). Qed.
Lemma lem3794659 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term374 _98585 s x) (h2 : term400 _98584 _98585 x'' s a f x b) : (term374 _98585 s x) = False.
Proof. exact (prop_ext (fun h3 : term374 _98585 s x => @lem3794628 _98584 _98585 x'' s a f x b h1 h2) (fun h3 : False => @lem3793097 _98585 s x h1)). Qed.
Lemma lem3794660 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term374 _98585 s x) (h2 : term400 _98584 _98585 x'' s a f x b) : False.
Proof. exact (EQ_MP (@lem3794659 _98584 _98585 x'' s a f x b h1 h2) (@lem3793097 _98585 s x h1)). Qed.
Lemma lem3794661 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term168 _98584 _98585 a f x b) (h2 : term303 _98584 _98585 c s x' a f x b) : (term168 _98584 _98585 a f x b) = False.
Proof. exact (prop_ext (fun h3 : term168 _98584 _98585 a f x b => @lem3794632 _98584 _98585 c s x' a f x b h1 h2) (fun h3 : False => @lem3793081 _98584 _98585 a f x b h1)). Qed.
Lemma lem3794662 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term168 _98584 _98585 a f x b) (h2 : term303 _98584 _98585 c s x' a f x b) : False.
Proof. exact (EQ_MP (@lem3794661 _98584 _98585 c s x' a f x b h1 h2) (@lem3793081 _98584 _98585 a f x b h1)). Qed.
Lemma lem3794663 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3794635 _98585 x' x h1 h2) (fun h3 : False => @lem3793067 _98585 x' x h2)). Qed.
Lemma lem3794664 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3794663 _98585 x' x h1 h2) (@lem3793067 _98585 x' x h2)). Qed.
Lemma lem3794665 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) (h2 : x' = x) : (term72 _98585 x' x) = False.
Proof. exact (prop_ext (fun h3 : term72 _98585 x' x => @lem3794664 _98585 x' x h1 h2) (fun h3 : False => @lem3793065 _98585 x' x h1)). Qed.
Lemma lem3794666 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3794665 _98585 x' x h1 h2) (@lem3793065 _98585 x' x h1)). Qed.
Lemma lem3794667 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term72 _98585 x' x) (h2 : s x') (h3 : term303 _98584 _98585 c s x' a f x b) : (s x') = False.
Proof. exact (prop_ext (fun h4 : s x' => @lem3794645 _98584 _98585 c s x' a f x b h1 h2 h3) (fun h4 : False => @lem3793051 _98585 s x' h2)). Qed.
Lemma lem3794668 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term72 _98585 x' x) (h2 : s x') (h3 : term303 _98584 _98585 c s x' a f x b) : False.
Proof. exact (EQ_MP (@lem3794667 _98584 _98585 c s x' a f x b h1 h2 h3) (@lem3793051 _98585 s x' h2)). Qed.
Lemma lem3794669 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term72 _98585 x' x) (h2 : s x') (h3 : term303 _98584 _98585 c s x' a f x b) : (term72 _98585 x' x) = False.
Proof. exact (prop_ext (fun h4 : term72 _98585 x' x => @lem3794668 _98584 _98585 c s x' a f x b h1 h2 h3) (fun h4 : False => @lem3793049 _98585 x' x h1)). Qed.
Lemma lem3794670 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term72 _98585 x' x) (h2 : s x') (h3 : term303 _98584 _98585 c s x' a f x b) : False.
Proof. exact (EQ_MP (@lem3794669 _98584 _98585 c s x' a f x b h1 h2 h3) (@lem3793049 _98585 x' x h1)). Qed.
Lemma lem3794671 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) (x' : _98585) (x : _98585) (h1 : term374 _98585 s x') (h2 : term303 _98584 _98585 c s x' a f x b) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3794648 _98584 _98585 c s a f b x' x h1 h2 h3) (fun h4 : False => @lem3793035 _98585 x' x h3)). Qed.
Lemma lem3794672 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) (x' : _98585) (x : _98585) (h1 : term374 _98585 s x') (h2 : term303 _98584 _98585 c s x' a f x b) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3794671 _98584 _98585 c s a f b x' x h1 h2 h3) (@lem3793035 _98585 x' x h3)). Qed.
Lemma lem3794673 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) (x' : _98585) (x : _98585) (h1 : term374 _98585 s x') (h2 : term303 _98584 _98585 c s x' a f x b) (h3 : x' = x) : (term374 _98585 s x') = False.
Proof. exact (prop_ext (fun h4 : term374 _98585 s x' => @lem3794672 _98584 _98585 c s a f b x' x h1 h2 h3) (fun h4 : False => @lem3793033 _98585 s x' h1)). Qed.
Lemma lem3794674 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) (x' : _98585) (x : _98585) (h1 : term374 _98585 s x') (h2 : term303 _98584 _98585 c s x' a f x b) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3794673 _98584 _98585 c s a f b x' x h1 h2 h3) (@lem3793033 _98585 s x' h1)). Qed.
Lemma lem3794675 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3794658 _98585 s x' h1 h2) (fun h3 : False => @lem3793019 _98585 s x' h2)). Qed.
Lemma lem3794676 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3794675 _98585 s x' h1 h2) (@lem3793019 _98585 s x' h2)). Qed.
Lemma lem3794677 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') (h2 : s x') : (term374 _98585 s x') = False.
Proof. exact (prop_ext (fun h3 : term374 _98585 s x' => @lem3794676 _98585 s x' h1 h2) (fun h3 : False => @lem3793017 _98585 s x' h1)). Qed.
Lemma lem3794678 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3794677 _98585 s x' h1 h2) (@lem3793017 _98585 s x' h1)). Qed.
Lemma lem3794679 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term374 _98585 s x) (h2 : term400 _98584 _98585 x'' s a f x b) : (term374 _98585 s x) = False.
Proof. exact (prop_ext (fun h3 : term374 _98585 s x => @lem3794660 _98584 _98585 x'' s a f x b h1 h2) (fun h3 : False => @lem3792906 _98585 s x h1)). Qed.
Lemma lem3794680 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term374 _98585 s x) (h2 : term400 _98584 _98585 x'' s a f x b) : False.
Proof. exact (EQ_MP (@lem3794679 _98584 _98585 x'' s a f x b h1 h2) (@lem3792906 _98585 s x h1)). Qed.
Lemma lem3794681 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term168 _98584 _98585 a f x b) (h2 : term303 _98584 _98585 c s x' a f x b) : (term168 _98584 _98585 a f x b) = False.
Proof. exact (prop_ext (fun h3 : term168 _98584 _98585 a f x b => @lem3794662 _98584 _98585 c s x' a f x b h1 h2) (fun h3 : False => @lem3792872 _98584 _98585 a f x b h1)). Qed.
Lemma lem3794682 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term168 _98584 _98585 a f x b) (h2 : term303 _98584 _98585 c s x' a f x b) : False.
Proof. exact (EQ_MP (@lem3794681 _98584 _98585 c s x' a f x b h1 h2) (@lem3792872 _98584 _98585 a f x b h1)). Qed.
Lemma lem3794683 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3794666 _98585 x' x h1 h2) (fun h3 : False => @lem3792843 _98585 x' x h2)). Qed.
Lemma lem3794684 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3794683 _98585 x' x h1 h2) (@lem3792843 _98585 x' x h2)). Qed.
Lemma lem3794685 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) (h2 : x' = x) : (term72 _98585 x' x) = False.
Proof. exact (prop_ext (fun h3 : term72 _98585 x' x => @lem3794684 _98585 x' x h1 h2) (fun h3 : False => @lem3792839 _98585 x' x h1)). Qed.
Lemma lem3794686 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3794685 _98585 x' x h1 h2) (@lem3792839 _98585 x' x h1)). Qed.
Lemma lem3794687 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term72 _98585 x' x) (h2 : s x') (h3 : term303 _98584 _98585 c s x' a f x b) : (s x') = False.
Proof. exact (prop_ext (fun h4 : s x' => @lem3794670 _98584 _98585 c s x' a f x b h1 h2 h3) (fun h4 : False => @lem3792810 _98585 s x' h2)). Qed.
Lemma lem3794688 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term72 _98585 x' x) (h2 : s x') (h3 : term303 _98584 _98585 c s x' a f x b) : False.
Proof. exact (EQ_MP (@lem3794687 _98584 _98585 c s x' a f x b h1 h2 h3) (@lem3792810 _98585 s x' h2)). Qed.
Lemma lem3794689 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term72 _98585 x' x) (h2 : s x') (h3 : term303 _98584 _98585 c s x' a f x b) : (term72 _98585 x' x) = False.
Proof. exact (prop_ext (fun h4 : term72 _98585 x' x => @lem3794688 _98584 _98585 c s x' a f x b h1 h2 h3) (fun h4 : False => @lem3792806 _98585 x' x h1)). Qed.
Lemma lem3794690 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term72 _98585 x' x) (h2 : s x') (h3 : term303 _98584 _98585 c s x' a f x b) : False.
Proof. exact (EQ_MP (@lem3794689 _98584 _98585 c s x' a f x b h1 h2 h3) (@lem3792806 _98585 x' x h1)). Qed.
Lemma lem3794691 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) (x' : _98585) (x : _98585) (h1 : term374 _98585 s x') (h2 : term303 _98584 _98585 c s x' a f x b) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3794674 _98584 _98585 c s a f b x' x h1 h2 h3) (fun h4 : False => @lem3792777 _98585 x' x h3)). Qed.
Lemma lem3794692 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) (x' : _98585) (x : _98585) (h1 : term374 _98585 s x') (h2 : term303 _98584 _98585 c s x' a f x b) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3794691 _98584 _98585 c s a f b x' x h1 h2 h3) (@lem3792777 _98585 x' x h3)). Qed.
Lemma lem3794693 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) (x' : _98585) (x : _98585) (h1 : term374 _98585 s x') (h2 : term303 _98584 _98585 c s x' a f x b) (h3 : x' = x) : (term374 _98585 s x') = False.
Proof. exact (prop_ext (fun h4 : term374 _98585 s x' => @lem3794692 _98584 _98585 c s a f b x' x h1 h2 h3) (fun h4 : False => @lem3792773 _98585 s x' h1)). Qed.
Lemma lem3794694 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) (x' : _98585) (x : _98585) (h1 : term374 _98585 s x') (h2 : term303 _98584 _98585 c s x' a f x b) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3794693 _98584 _98585 c s a f b x' x h1 h2 h3) (@lem3792773 _98585 s x' h1)). Qed.
Lemma lem3794695 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3794678 _98585 s x' h1 h2) (fun h3 : False => @lem3792744 _98585 s x' h2)). Qed.
Lemma lem3794696 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3794695 _98585 s x' h1 h2) (@lem3792744 _98585 s x' h2)). Qed.
Lemma lem3794697 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') (h2 : s x') : (term374 _98585 s x') = False.
Proof. exact (prop_ext (fun h3 : term374 _98585 s x' => @lem3794696 _98585 s x' h1 h2) (fun h3 : False => @lem3792740 _98585 s x' h1)). Qed.
Lemma lem3794698 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3794697 _98585 s x' h1 h2) (@lem3792740 _98585 s x' h1)). Qed.
Lemma lem3794699 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term374 _98585 s x) (h2 : term400 _98584 _98585 x'' s a f x b) : (term374 _98585 s x) = False.
Proof. exact (prop_ext (fun h3 : term374 _98585 s x => @lem3794680 _98584 _98585 x'' s a f x b h1 h2) (fun h3 : False => @lem3792906 _98585 s x h1)). Qed.
Lemma lem3794700 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term374 _98585 s x) (h2 : term400 _98584 _98585 x'' s a f x b) : False.
Proof. exact (EQ_MP (@lem3794699 _98584 _98585 x'' s a f x b h1 h2) (@lem3792906 _98585 s x h1)). Qed.
Lemma lem3794701 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term168 _98584 _98585 a f x b) (h2 : term303 _98584 _98585 c s x' a f x b) : (term168 _98584 _98585 a f x b) = False.
Proof. exact (prop_ext (fun h3 : term168 _98584 _98585 a f x b => @lem3794682 _98584 _98585 c s x' a f x b h1 h2) (fun h3 : False => @lem3792872 _98584 _98585 a f x b h1)). Qed.
Lemma lem3794702 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term168 _98584 _98585 a f x b) (h2 : term303 _98584 _98585 c s x' a f x b) : False.
Proof. exact (EQ_MP (@lem3794701 _98584 _98585 c s x' a f x b h1 h2) (@lem3792872 _98584 _98585 a f x b h1)). Qed.
Lemma lem3794703 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3794686 _98585 x' x h1 h2) (fun h3 : False => @lem3792843 _98585 x' x h2)). Qed.
Lemma lem3794704 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3794703 _98585 x' x h1 h2) (@lem3792843 _98585 x' x h2)). Qed.
Lemma lem3794705 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) (h2 : x' = x) : (term72 _98585 x' x) = False.
Proof. exact (prop_ext (fun h3 : term72 _98585 x' x => @lem3794704 _98585 x' x h1 h2) (fun h3 : False => @lem3792839 _98585 x' x h1)). Qed.
Lemma lem3794706 {_98585 : Type'} (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3794705 _98585 x' x h1 h2) (@lem3792839 _98585 x' x h1)). Qed.
Lemma lem3794707 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term72 _98585 x' x) (h2 : s x') (h3 : term303 _98584 _98585 c s x' a f x b) : (s x') = False.
Proof. exact (prop_ext (fun h4 : s x' => @lem3794690 _98584 _98585 c s x' a f x b h1 h2 h3) (fun h4 : False => @lem3792810 _98585 s x' h2)). Qed.
Lemma lem3794708 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term72 _98585 x' x) (h2 : s x') (h3 : term303 _98584 _98585 c s x' a f x b) : False.
Proof. exact (EQ_MP (@lem3794707 _98584 _98585 c s x' a f x b h1 h2 h3) (@lem3792810 _98585 s x' h2)). Qed.
Lemma lem3794709 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term72 _98585 x' x) (h2 : s x') (h3 : term303 _98584 _98585 c s x' a f x b) : (term72 _98585 x' x) = False.
Proof. exact (prop_ext (fun h4 : term72 _98585 x' x => @lem3794708 _98584 _98585 c s x' a f x b h1 h2 h3) (fun h4 : False => @lem3792806 _98585 x' x h1)). Qed.
Lemma lem3794710 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term72 _98585 x' x) (h2 : s x') (h3 : term303 _98584 _98585 c s x' a f x b) : False.
Proof. exact (EQ_MP (@lem3794709 _98584 _98585 c s x' a f x b h1 h2 h3) (@lem3792806 _98585 x' x h1)). Qed.
Lemma lem3794711 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) (x' : _98585) (x : _98585) (h1 : term374 _98585 s x') (h2 : term303 _98584 _98585 c s x' a f x b) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3794694 _98584 _98585 c s a f b x' x h1 h2 h3) (fun h4 : False => @lem3792777 _98585 x' x h3)). Qed.
Lemma lem3794712 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) (x' : _98585) (x : _98585) (h1 : term374 _98585 s x') (h2 : term303 _98584 _98585 c s x' a f x b) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3794711 _98584 _98585 c s a f b x' x h1 h2 h3) (@lem3792777 _98585 x' x h3)). Qed.
Lemma lem3794713 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) (x' : _98585) (x : _98585) (h1 : term374 _98585 s x') (h2 : term303 _98584 _98585 c s x' a f x b) (h3 : x' = x) : (term374 _98585 s x') = False.
Proof. exact (prop_ext (fun h4 : term374 _98585 s x' => @lem3794712 _98584 _98585 c s a f b x' x h1 h2 h3) (fun h4 : False => @lem3792773 _98585 s x' h1)). Qed.
Lemma lem3794714 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) (x' : _98585) (x : _98585) (h1 : term374 _98585 s x') (h2 : term303 _98584 _98585 c s x' a f x b) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3794713 _98584 _98585 c s a f b x' x h1 h2 h3) (@lem3792773 _98585 s x' h1)). Qed.
Lemma lem3794715 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3794698 _98585 s x' h1 h2) (fun h3 : False => @lem3792744 _98585 s x' h2)). Qed.
Lemma lem3794716 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3794715 _98585 s x' h1 h2) (@lem3792744 _98585 s x' h2)). Qed.
Lemma lem3794717 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') (h2 : s x') : (term374 _98585 s x') = False.
Proof. exact (prop_ext (fun h3 : term374 _98585 s x' => @lem3794716 _98585 s x' h1 h2) (fun h3 : False => @lem3792740 _98585 s x' h1)). Qed.
Lemma lem3794718 {_98585 : Type'} (s : _98585 -> Prop) (x' : _98585) (h1 : term374 _98585 s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3794717 _98585 s x' h1 h2) (@lem3792740 _98585 s x' h1)). Qed.
Lemma lem3794719 {_98584 _98585 : Type'} (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term400 _98584 _98585 x'' s a f x b) : False.
Proof. exact (or_elim (@lem3792705 _98584 _98585 x'' s a f x b h1) (fun h0 : term374 _98585 s x => @lem3794700 _98584 _98585 x'' s a f x b h0 h1) (fun h0 : term363 _98584 _98585 s x'' b a f x => @lem3794625 _98584 _98585 x'' s a f x b h0 h1)). Qed.
Lemma lem3794720 {_98584 _98585 : Type'} (c : _98584) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) (s : _98585 -> Prop) (x' : _98585) (x : _98585) (h1 : term72 _98585 x' x) (h2 : term303 _98584 _98585 c s x' a f x b) (h3 : term191 _98585 s x' x) : False.
Proof. exact (or_elim (@lem3792697 _98585 s x' x h3) (fun h0 : s x' => @lem3794710 _98584 _98585 c s x' a f x b h1 h0 h2) (fun h0 : x' = x => @lem3794706 _98585 x' x h1 h0)). Qed.
Lemma lem3794721 {_98584 _98585 : Type'} (c : _98584) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) (s : _98585 -> Prop) (x' : _98585) (x : _98585) (h1 : term374 _98585 s x') (h2 : term303 _98584 _98585 c s x' a f x b) (h3 : term191 _98585 s x' x) : False.
Proof. exact (or_elim (@lem3792697 _98585 s x' x h3) (fun h0 : s x' => @lem3794718 _98585 s x' h1 h0) (fun h0 : x' = x => @lem3794714 _98584 _98585 c s a f b x' x h1 h2 h0)). Qed.
Lemma lem3794722 {_98584 _98585 : Type'} (c : _98584) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) (s : _98585 -> Prop) (x' : _98585) (x : _98585) (h1 : term303 _98584 _98585 c s x' a f x b) (h2 : term191 _98585 s x' x) : False.
Proof. exact (or_elim (@lem3792696 _98585 s x' x h2) (fun h0 : term374 _98585 s x' => @lem3794721 _98584 _98585 c a f b s x' x h0 h1 h2) (fun h0 : term72 _98585 x' x => @lem3794720 _98584 _98585 c a f b s x' x h0 h1 h2)). Qed.
Lemma lem3794723 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (x' : _98585) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term303 _98584 _98585 c s x' a f x b) : False.
Proof. exact (or_elim (@lem3792686 _98584 _98585 c s x' a f x b h1) (fun h0 : term191 _98585 s x' x => @lem3794722 _98584 _98585 c a f b s x' x h1 h0) (fun h0 : term168 _98584 _98585 a f x b => @lem3794702 _98584 _98585 c s x' a f x b h0 h1)). Qed.
Lemma lem3794724 {_98584 _98585 : Type'} (c : _98584) (x' : _98585) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term443 _98584 _98585 c x' x'' s a f x b) : False.
Proof. exact (or_elim (@lem3792683 _98584 _98585 c x' x'' s a f x b h1) (fun h0 : term303 _98584 _98585 c s x' a f x b => @lem3794723 _98584 _98585 c s x' a f x b h0) (fun h0 : term400 _98584 _98585 x'' s a f x b => @lem3794719 _98584 _98585 x'' s a f x b h0)). Qed.
Lemma lem3794725 {_98584 _98585 : Type'} (c : _98584) (x' : _98585) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term443 _98584 _98585 c x' x'' s a f x b) : (term443 _98584 _98585 c x' x'' s a f x b) = False.
Proof. exact (prop_ext (fun h2 : term443 _98584 _98585 c x' x'' s a f x b => @lem3794724 _98584 _98585 c x' x'' s a f x b h1) (fun h2 : False => @lem3792683 _98584 _98585 c x' x'' s a f x b h1)). Qed.
Lemma lem3794726 {_98584 _98585 : Type'} (c : _98584) (x' : _98585) (x'' : _98584 -> _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term443 _98584 _98585 c x' x'' s a f x b) : False.
Proof. exact (EQ_MP (@lem3794725 _98584 _98585 c x' x'' s a f x b h1) (@lem3792683 _98584 _98585 c x' x'' s a f x b h1)). Qed.
Lemma lem3794727 {_98584 _98585 : Type'} (c : _98584) (x' : _98585) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term446 _98584 _98585 c x' s a f x b) : False.
Proof. exact (ex_elim (@lem3792488 _98584 _98585 c x' s a f x b h1) (fun x'' : _98584 -> _98585 => fun h0 : term445 _98584 _98585 c x' s a f x b x'' => @lem3794726 _98584 _98585 c x' x'' s a f x b h0)). Qed.
Lemma lem3794728 {_98584 _98585 : Type'} (c : _98584) (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term448 _98584 _98585 c s a f x b) : False.
Proof. exact (ex_elim (@lem3792487 _98584 _98585 c s a f x b h1) (fun x' : _98585 => fun h0 : term447 _98584 _98585 c s a f x b x' => @lem3794727 _98584 _98585 c x' s a f x b h0)). Qed.
Lemma lem3794729 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term144 _98584 _98585 s a f x b) : False.
Proof. exact (ex_elim (@lem3792486 _98584 _98585 s a f x b h1) (fun c : _98584 => fun h0 : term449 _98584 _98585 s a f x b c => @lem3794728 _98584 _98585 c s a f x b h0)). Qed.
Lemma lem3794730 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term144 _98584 _98585 s a f x b) : (term144 _98584 _98585 s a f x b) = False.
Proof. exact (prop_ext (fun h2 : term144 _98584 _98585 s a f x b => @lem3794729 _98584 _98585 s a f x b h1) (fun h2 : False => @lem3791701 _98584 _98585 s a f x b h1)). Qed.
Lemma lem3794731 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term144 _98584 _98585 s a f x b) : False.
Proof. exact (EQ_MP (@lem3794730 _98584 _98585 s a f x b h1) (@lem3791701 _98584 _98585 s a f x b h1)). Qed.
Lemma lem3794732 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : term143 _98584 _98585 s a f x b.
Proof. exact (fun h0 : term144 _98584 _98585 s a f x b => @lem3794731 _98584 _98585 s a f x b h0). Qed.
Lemma lem3794733 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term121 _98584 _98585 s b a f x) = (term100 _98584 _98585 s a f x b).
Proof. exact (EQ_MP (@lem3791700 _98584 _98585 s a f x b) (@lem3794732 _98584 _98585 s a f x b)). Qed.
Lemma lem3794738 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : term126 _98584 _98585 a f x b.
Proof. exact (fun s : _98585 -> Prop => @lem3794733 _98584 _98585 s a f x b). Qed.
Lemma lem3794743 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : term130 _98584 _98585 f x b.
Proof. exact (fun a : _98584 => @lem3794738 _98584 _98585 a f x b). Qed.
Lemma lem3794748 {_98584 _98585 : Type'} (x : _98585) (b : _98584) : term134 _98584 _98585 x b.
Proof. exact (fun f : type1467 _98584 _98585 => @lem3794743 _98584 _98585 f x b). Qed.
Lemma lem3794753 {_98584 _98585 : Type'} (b : _98584) : term138 _98584 _98585 b.
Proof. exact (fun x : _98585 => @lem3794748 _98584 _98585 x b). Qed.
Lemma lem3794758 {_98584 _98585 : Type'} : term142 _98584 _98585.
Proof. exact (fun b : _98584 => @lem3794753 _98584 _98585 b). Qed.
Lemma lem3794759 {_98584 _98585 : Type'} : term141 _98584 _98585.
Proof. exact (EQ_MP (@lem3791696 _98584 _98585) (@lem3794758 _98584 _98585)). Qed.
Lemma lem3794760 {_98584 _98585 : Type'} (b : _98584) : term556 _98584 _98585 b.
Proof. exact (@lem3794759 _98584 _98585 b). Qed.
Lemma lem3794761 {_98584 _98585 : Type'} (b : _98584) : (term556 _98584 _98585 b) = (term137 _98584 _98585 b).
Proof. exact (eq_refl (term556 _98584 _98585 b)). Qed.
Lemma lem3794762 {_98584 _98585 : Type'} (b : _98584) : term137 _98584 _98585 b.
Proof. exact (EQ_MP (@lem3794761 _98584 _98585 b) (@lem3794760 _98584 _98585 b)). Qed.
Lemma lem3794763 {_98584 _98585 : Type'} (b : _98584) (x : _98585) : term557 _98584 _98585 b x.
Proof. exact (@lem3794762 _98584 _98585 b x). Qed.
Lemma lem3794764 {_98584 _98585 : Type'} (x : _98585) (b : _98584) : (term557 _98584 _98585 b x) = (term133 _98584 _98585 x b).
Proof. exact (eq_refl (term557 _98584 _98585 b x)). Qed.
Lemma lem3794765 {_98584 _98585 : Type'} (x : _98585) (b : _98584) : term133 _98584 _98585 x b.
Proof. exact (EQ_MP (@lem3794764 _98584 _98585 x b) (@lem3794763 _98584 _98585 b x)). Qed.
Lemma lem3794766 {_98584 _98585 : Type'} (x : _98585) (b : _98584) (f : type1467 _98584 _98585) : term558 _98584 _98585 x b f.
Proof. exact (@lem3794765 _98584 _98585 x b f). Qed.
Lemma lem3794767 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term558 _98584 _98585 x b f) = (term129 _98584 _98585 f x b).
Proof. exact (eq_refl (term558 _98584 _98585 x b f)). Qed.
Lemma lem3794768 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : term129 _98584 _98585 f x b.
Proof. exact (EQ_MP (@lem3794767 _98584 _98585 f x b) (@lem3794766 _98584 _98585 x b f)). Qed.
Lemma lem3794769 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (a : _98584) : term559 _98584 _98585 f x b a.
Proof. exact (@lem3794768 _98584 _98585 f x b a). Qed.
Lemma lem3794770 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term559 _98584 _98585 f x b a) = (term125 _98584 _98585 a f x b).
Proof. exact (eq_refl (term559 _98584 _98585 f x b a)). Qed.
Lemma lem3794771 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : term125 _98584 _98585 a f x b.
Proof. exact (EQ_MP (@lem3794770 _98584 _98585 a f x b) (@lem3794769 _98584 _98585 f x b a)). Qed.
Lemma lem3794772 {_98584 _98585 : Type'} (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (s : _98585 -> Prop) : term560 _98584 _98585 a f x b s.
Proof. exact (@lem3794771 _98584 _98585 a f x b s). Qed.
Lemma lem3794773 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term560 _98584 _98585 a f x b s) = (term102 _98584 _98585 s a f x b).
Proof. exact (eq_refl (term560 _98584 _98585 a f x b s)). Qed.
Lemma lem3794774 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : term102 _98584 _98585 s a f x b.
Proof. exact (EQ_MP (@lem3794773 _98584 _98585 s a f x b) (@lem3794772 _98584 _98585 a f x b s)). Qed.
Lemma lem3794776 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : term102 _98584 _98585 s a f x b.
Proof. exact (@lem3791420 _98584 _98585 s a f x b (@lem3794774 _98584 _98585 s a f x b)). Qed.
Lemma lem3794777 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term103 _98584 _98585 s a f x b) : False.
Proof. exact (@lem3794776 _98584 _98585 s a f x b (@lem3791404 _98584 _98585 s a f x b h1)). Qed.
Lemma lem3794778 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term103 _98584 _98585 s a f x b) : (term103 _98584 _98585 s a f x b) = False.
Proof. exact (prop_ext (fun h2 : term103 _98584 _98585 s a f x b => @lem3794777 _98584 _98585 s a f x b h1) (fun h2 : False => @lem3791404 _98584 _98585 s a f x b h1)). Qed.
Lemma lem3794779 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) (h1 : term103 _98584 _98585 s a f x b) : False.
Proof. exact (EQ_MP (@lem3794778 _98584 _98585 s a f x b h1) (@lem3791404 _98584 _98585 s a f x b h1)). Qed.
Lemma lem3794780 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : term102 _98584 _98585 s a f x b.
Proof. exact (fun h0 : term103 _98584 _98585 s a f x b => @lem3794779 _98584 _98585 s a f x b h0). Qed.
Lemma lem3794781 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term86 _98584 _98585 s b a f x) = (term100 _98584 _98585 s a f x b).
Proof. exact (EQ_MP (@lem3791403 _98584 _98585 s a f x b) (@lem3794780 _98584 _98585 s a f x b)). Qed.
Lemma lem3794782 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term61 _98584 _98585 s b a f x) = (term68 _98584 _98585 s a f x b).
Proof. exact (EQ_MP (@lem3791399 _98584 _98585 s a f x b) (@lem3794781 _98584 _98585 s a f x b)). Qed.
Lemma lem3794783 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (x : _98585) (b : _98584) : (term29 _98584 _98585 s b a f x) = (term67 _98584 _98585 s a f x b).
Proof. exact (EQ_MP (@lem3791249 _98584 _98585 s a f x b) (@lem3794782 _98584 _98585 s a f x b)). Qed.
Lemma lem3794786 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) : (term31 _98584 _98585 s b a f) = (term561 _98584 _98585 s a f b).
Proof. exact (fun_ext (fun x : _98585 => @lem3794783 _98584 _98585 s a f x b)). Qed.
Lemma lem3794787 {_98584 _98585 : Type'} (s : _98585 -> Prop) (a : _98584) (f : type1467 _98584 _98585) (b : _98584) : (term32 _98584 _98585 s b a f) = (term35 _98584 _98585 s a f b).
Proof. exact (MK_COMB (@lem3791156 _98585) (@lem3794786 _98584 _98585 s a f b)). Qed.
Lemma lem3794792 {_98584 _98585 : Type'} (s : _98585 -> Prop) (f : type1467 _98584 _98585) (b : _98584) : term39 _98584 _98585 s f b.
Proof. exact (fun a : _98584 => @lem3794787 _98584 _98585 s a f b). Qed.
Lemma lem3794797 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) (b : _98584) : term43 _98584 _98585 f b.
Proof. exact (fun s : _98585 -> Prop => @lem3794792 _98584 _98585 s f b). Qed.
Lemma lem3794802 {_98584 _98585 : Type'} (f : type1467 _98584 _98585) : term47 _98584 _98585 f.
Proof. exact (fun b : _98584 => @lem3794797 _98584 _98585 f b). Qed.
Lemma lem3794807 {_98584 _98585 : Type'} : term51 _98584 _98585.
Proof. exact (fun f : type1467 _98584 _98585 => @lem3794802 _98584 _98585 f). Qed.
Lemma lem3794808 {_98584 _98585 : Type'} : term50 _98584 _98585.
Proof. exact (EQ_MP (@lem3791155 _98584 _98585) (@lem3794807 _98584 _98585)). Qed.
