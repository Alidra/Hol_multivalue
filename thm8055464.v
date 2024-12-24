Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8055464_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm1857_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm8049023_spec.
Lemma lem8054026 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem8054027 {_143007 _143009 : Type'} (s : type56 _143007 _143009) (t : type56 _143007 _143009) : (s = t) = (term1 _143007 _143009 s t).
Proof. exact (@lem8054026 (type24 _143007 _143009) s t). Qed.
Lemma lem8054028 {_143007 _143009 : Type'} (f : type56 _143007 _143009) : (f = (@EMPTY ((cart _143007 _143009) -> Prop))) = (term2 _143007 _143009 f).
Proof. exact (@lem8054027 _143007 _143009 f (@EMPTY ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054037 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8054038 {_143007 _143009 : Type'} (f : type56 _143007 _143009) : (term3 _143007 _143009 f) = (term4 _143007 _143009 f).
Proof. exact (MK_COMB (@lem8054037) (@lem8054028 _143007 _143009 f)). Qed.
Lemma lem8054039 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8054040 {_143007 _143009 : Type'} (f : type56 _143007 _143009) : (term5 _143007 _143009 f) = (term6 _143007 _143009 f).
Proof. exact (MK_COMB (@lem8054039) (@lem8054038 _143007 _143009 f)). Qed.
Lemma lem8054063 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term7 _143007 _143008 _143009 f s) = (term7 _143007 _143008 _143009 f s).
Proof. exact (eq_refl (term7 _143007 _143008 _143009 f s)). Qed.
Lemma lem8054064 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term8 _143007 _143008 _143009 f s) = (term9 _143007 _143008 _143009 f s).
Proof. exact (MK_COMB (@lem8054040 _143007 _143009 f) (@lem8054063 _143007 _143008 _143009 f s)). Qed.
Lemma lem8054067 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term9 _143007 _143008 _143009 f s) = (term8 _143007 _143008 _143009 f s).
Proof. exact (SYM (@lem8054064 _143007 _143008 _143009 f s)). Qed.
Lemma lem8054077 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8054078 {_143007 _143009 : Type'} (P : type56 _143007 _143009) (x : type24 _143007 _143009) : (@IN ((cart _143007 _143009) -> Prop) x P) = (P x).
Proof. exact (@lem8054077 (type24 _143007 _143009) P x). Qed.
Lemma lem8054079 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x : type24 _143007 _143009) : (@IN ((cart _143007 _143009) -> Prop) x f) = (f x).
Proof. exact (@lem8054078 _143007 _143009 f x). Qed.
Lemma lem8054080 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8054081 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x : type24 _143007 _143009) : (term10 _143007 _143009 x f) = (term11 _143007 _143009 f x).
Proof. exact (MK_COMB (@lem8054080) (@lem8054079 _143007 _143009 f x)). Qed.
Lemma lem8054083 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem8054084 {_143007 _143009 : Type'} (x : type24 _143007 _143009) : (@IN ((cart _143007 _143009) -> Prop) x (@EMPTY ((cart _143007 _143009) -> Prop))) = False.
Proof. exact (@lem8054083 (type24 _143007 _143009) x). Qed.
Lemma lem8054085 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x : type24 _143007 _143009) : ((@IN ((cart _143007 _143009) -> Prop) x f) = (@IN ((cart _143007 _143009) -> Prop) x (@EMPTY ((cart _143007 _143009) -> Prop)))) = ((f x) = False).
Proof. exact (MK_COMB (@lem8054081 _143007 _143009 f x) (@lem8054084 _143007 _143009 x)). Qed.
Lemma lem8054087 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem8054088 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x : type24 _143007 _143009) : ((f x) = False) = (term12 _143007 _143009 f x).
Proof. exact (@lem8054087 (f x)). Qed.
Lemma lem8054089 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x : type24 _143007 _143009) : ((@IN ((cart _143007 _143009) -> Prop) x f) = (@IN ((cart _143007 _143009) -> Prop) x (@EMPTY ((cart _143007 _143009) -> Prop)))) = (term12 _143007 _143009 f x).
Proof. exact (TRANS (@lem8054085 _143007 _143009 f x) (@lem8054088 _143007 _143009 f x)). Qed.
Lemma lem8054090 {_143007 _143009 : Type'} (f : type56 _143007 _143009) : (term13 _143007 _143009 f) = (term14 _143007 _143009 f).
Proof. exact (fun_ext (fun x : type24 _143007 _143009 => @lem8054089 _143007 _143009 f x)). Qed.
Lemma lem8054091 {_143007 _143009 : Type'} : (@all ((cart _143007 _143009) -> Prop)) = (@all ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054092 {_143007 _143009 : Type'} (f : type56 _143007 _143009) : (term2 _143007 _143009 f) = (term15 _143007 _143009 f).
Proof. exact (MK_COMB (@lem8054091 _143007 _143009) (@lem8054090 _143007 _143009 f)). Qed.
Lemma lem8054097 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8054098 {_143007 _143009 : Type'} (f : type56 _143007 _143009) : (term4 _143007 _143009 f) = (term16 _143007 _143009 f).
Proof. exact (MK_COMB (@lem8054097) (@lem8054092 _143007 _143009 f)). Qed.
Lemma lem8054099 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8054100 {_143007 _143009 : Type'} (f : type56 _143007 _143009) : (term6 _143007 _143009 f) = (term17 _143007 _143009 f).
Proof. exact (MK_COMB (@lem8054099) (@lem8054098 _143007 _143009 f)). Qed.
Lemma lem8054114 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8054115 {_143007 _143008 : Type'} (P : type24 _143007 _143008) (x : cart _143007 _143008) : (@IN (cart _143007 _143008) x P) = (P x).
Proof. exact (@lem8054114 (cart _143007 _143008) P x). Qed.
Lemma lem8054116 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (@IN (cart _143007 _143008) x s) = (s x).
Proof. exact (@lem8054115 _143007 _143008 s x). Qed.
Lemma lem8054117 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8054118 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term18 _143007 _143008 x s) = (term19 _143007 _143008 s x).
Proof. exact (MK_COMB (@lem8054117) (@lem8054116 _143007 _143008 s x)). Qed.
Lemma lem8054120 {A : Type'} (s : type686 A) (x : A) : (term20 A x s) = (term21 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem8054121 {_143007 _143009 : Type'} (s : type56 _143007 _143009) (x : cart _143007 _143009) : (term22 _143007 _143009 x s) = (term23 _143007 _143009 s x).
Proof. exact (@lem8054120 (cart _143007 _143009) s x). Qed.
Lemma lem8054122 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term22 _143007 _143009 y f) = (term23 _143007 _143009 f y).
Proof. exact (@lem8054121 _143007 _143009 f y). Qed.
Lemma lem8054130 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8054131 {_143007 _143009 : Type'} (P : type56 _143007 _143009) (x : type24 _143007 _143009) : (@IN ((cart _143007 _143009) -> Prop) x P) = (P x).
Proof. exact (@lem8054130 (type24 _143007 _143009) P x). Qed.
Lemma lem8054132 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) : (@IN ((cart _143007 _143009) -> Prop) t f) = (f t).
Proof. exact (@lem8054131 _143007 _143009 f t). Qed.
Lemma lem8054133 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8054134 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) : (term24 _143007 _143009 t f) = (term25 _143007 _143009 f t).
Proof. exact (MK_COMB (@lem8054133) (@lem8054132 _143007 _143009 f t)). Qed.
Lemma lem8054136 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8054137 {_143007 _143009 : Type'} (P : type24 _143007 _143009) (x : cart _143007 _143009) : (@IN (cart _143007 _143009) x P) = (P x).
Proof. exact (@lem8054136 (cart _143007 _143009) P x). Qed.
Lemma lem8054138 {_143007 _143009 : Type'} (t : type24 _143007 _143009) (y : cart _143007 _143009) : (@IN (cart _143007 _143009) y t) = (t y).
Proof. exact (@lem8054137 _143007 _143009 t y). Qed.
Lemma lem8054139 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term26 _143007 _143009 f y t) = (term27 _143007 _143009 f t y).
Proof. exact (MK_COMB (@lem8054134 _143007 _143009 f t) (@lem8054138 _143007 _143009 t y)). Qed.
Lemma lem8054142 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term28 _143007 _143009 f y) = (term29 _143007 _143009 f y).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8054139 _143007 _143009 f t y)). Qed.
Lemma lem8054143 {_143007 _143009 : Type'} : (@all ((cart _143007 _143009) -> Prop)) = (@all ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054144 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term23 _143007 _143009 f y) = (term30 _143007 _143009 f y).
Proof. exact (MK_COMB (@lem8054143 _143007 _143009) (@lem8054142 _143007 _143009 f y)). Qed.
Lemma lem8054149 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term22 _143007 _143009 y f) = (term30 _143007 _143009 f y).
Proof. exact (TRANS (@lem8054122 _143007 _143009 f y) (@lem8054144 _143007 _143009 f y)). Qed.
Lemma lem8054150 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term31 _143007 _143008 _143009 x s y f) = (term32 _143007 _143008 _143009 s x f y).
Proof. exact (MK_COMB (@lem8054118 _143007 _143008 s x) (@lem8054149 _143007 _143009 f y)). Qed.
Lemma lem8054153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8054154 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term33 _143007 _143008 _143009 x s y f) = (term34 _143007 _143008 _143009 s x f y).
Proof. exact (MK_COMB (@lem8054153) (@lem8054150 _143007 _143008 _143009 s x f y)). Qed.
Lemma lem8054162 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8054163 {_143007 _143009 : Type'} (P : type56 _143007 _143009) (x : type24 _143007 _143009) : (@IN ((cart _143007 _143009) -> Prop) x P) = (P x).
Proof. exact (@lem8054162 (type24 _143007 _143009) P x). Qed.
Lemma lem8054164 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) : (@IN ((cart _143007 _143009) -> Prop) t f) = (f t).
Proof. exact (@lem8054163 _143007 _143009 f t). Qed.
Lemma lem8054165 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8054166 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) : (term24 _143007 _143009 t f) = (term25 _143007 _143009 f t).
Proof. exact (MK_COMB (@lem8054165) (@lem8054164 _143007 _143009 f t)). Qed.
Lemma lem8054170 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8054171 {_143007 _143008 : Type'} (P : type24 _143007 _143008) (x : cart _143007 _143008) : (@IN (cart _143007 _143008) x P) = (P x).
Proof. exact (@lem8054170 (cart _143007 _143008) P x). Qed.
Lemma lem8054172 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (@IN (cart _143007 _143008) x s) = (s x).
Proof. exact (@lem8054171 _143007 _143008 s x). Qed.
Lemma lem8054173 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8054174 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term18 _143007 _143008 x s) = (term19 _143007 _143008 s x).
Proof. exact (MK_COMB (@lem8054173) (@lem8054172 _143007 _143008 s x)). Qed.
Lemma lem8054176 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8054177 {_143007 _143009 : Type'} (P : type24 _143007 _143009) (x : cart _143007 _143009) : (@IN (cart _143007 _143009) x P) = (P x).
Proof. exact (@lem8054176 (cart _143007 _143009) P x). Qed.
Lemma lem8054178 {_143007 _143009 : Type'} (t : type24 _143007 _143009) (y : cart _143007 _143009) : (@IN (cart _143007 _143009) y t) = (t y).
Proof. exact (@lem8054177 _143007 _143009 t y). Qed.
Lemma lem8054179 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term35 _143007 _143008 _143009 x s y t) = (term36 _143007 _143008 _143009 s x t y).
Proof. exact (MK_COMB (@lem8054174 _143007 _143008 s x) (@lem8054178 _143007 _143009 t y)). Qed.
Lemma lem8054182 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term37 _143007 _143008 _143009 f x s y t) = (term38 _143007 _143008 _143009 f s x t y).
Proof. exact (MK_COMB (@lem8054166 _143007 _143009 f t) (@lem8054179 _143007 _143008 _143009 s x t y)). Qed.
Lemma lem8054185 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term39 _143007 _143008 _143009 f x s y) = (term40 _143007 _143008 _143009 f s x y).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8054182 _143007 _143008 _143009 f s x t y)). Qed.
Lemma lem8054186 {_143007 _143009 : Type'} : (@all ((cart _143007 _143009) -> Prop)) = (@all ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054187 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term41 _143007 _143008 _143009 f x s y) = (term42 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054186 _143007 _143009) (@lem8054185 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054192 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : ((term31 _143007 _143008 _143009 x s y f) = (term41 _143007 _143008 _143009 f x s y)) = ((term32 _143007 _143008 _143009 s x f y) = (term42 _143007 _143008 _143009 f s x y)).
Proof. exact (MK_COMB (@lem8054154 _143007 _143008 _143009 s x f y) (@lem8054187 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054195 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term43 _143007 _143008 _143009 f x s) = (term44 _143007 _143008 _143009 f s x).
Proof. exact (fun_ext (fun y : cart _143007 _143009 => @lem8054192 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054196 {_143007 _143009 : Type'} : (@all (cart _143007 _143009)) = (@all (cart _143007 _143009)).
Proof. exact (eq_refl (@all (cart _143007 _143009))). Qed.
Lemma lem8054197 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term45 _143007 _143008 _143009 f x s) = (term46 _143007 _143008 _143009 f s x).
Proof. exact (MK_COMB (@lem8054196 _143007 _143009) (@lem8054195 _143007 _143008 _143009 f s x)). Qed.
Lemma lem8054202 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term47 _143007 _143008 _143009 f s) = (term48 _143007 _143008 _143009 f s).
Proof. exact (fun_ext (fun x : cart _143007 _143008 => @lem8054197 _143007 _143008 _143009 f s x)). Qed.
Lemma lem8054203 {_143007 _143008 : Type'} : (@all (cart _143007 _143008)) = (@all (cart _143007 _143008)).
Proof. exact (eq_refl (@all (cart _143007 _143008))). Qed.
Lemma lem8054204 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term7 _143007 _143008 _143009 f s) = (term49 _143007 _143008 _143009 f s).
Proof. exact (MK_COMB (@lem8054203 _143007 _143008) (@lem8054202 _143007 _143008 _143009 f s)). Qed.
Lemma lem8054209 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term9 _143007 _143008 _143009 f s) = (term50 _143007 _143008 _143009 f s).
Proof. exact (MK_COMB (@lem8054100 _143007 _143009 f) (@lem8054204 _143007 _143008 _143009 f s)). Qed.
Lemma lem8054212 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term50 _143007 _143008 _143009 f s) = (term9 _143007 _143008 _143009 f s).
Proof. exact (SYM (@lem8054209 _143007 _143008 _143009 f s)). Qed.
Lemma lem8054214 (p : Prop) : p = (term51 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8054215 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term50 _143007 _143008 _143009 f s) = (term52 _143007 _143008 _143009 f s).
Proof. exact (@lem8054214 (term50 _143007 _143008 _143009 f s)). Qed.
Lemma lem8054216 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term52 _143007 _143008 _143009 f s) = (term50 _143007 _143008 _143009 f s).
Proof. exact (SYM (@lem8054215 _143007 _143008 _143009 f s)). Qed.
Lemma lem8054217 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (h1 : term53 _143007 _143008 _143009 f s) : term53 _143007 _143008 _143009 f s.
Proof. exact (h1). Qed.
Lemma lem8054220 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (h1 : term52 _143007 _143008 _143009 f s) : term52 _143007 _143008 _143009 f s.
Proof. exact (h1). Qed.
Lemma lem8054221 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : term54 _143007 _143008 _143009 f s.
Proof. exact (fun h0 : term52 _143007 _143008 _143009 f s => @lem8054220 _143007 _143008 _143009 f s h0). Qed.
Lemma lem8054222 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (h1 : term54 _143007 _143008 _143009 f s) : term54 _143007 _143008 _143009 f s.
Proof. exact (h1). Qed.
Lemma lem8054223 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (h1 : term52 _143007 _143008 _143009 f s) : term52 _143007 _143008 _143009 f s.
Proof. exact (h1). Qed.
Lemma lem8054224 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (h1 : term52 _143007 _143008 _143009 f s) (h2 : term54 _143007 _143008 _143009 f s) : term52 _143007 _143008 _143009 f s.
Proof. exact (@lem8054222 _143007 _143008 _143009 f s h2 (@lem8054223 _143007 _143008 _143009 f s h1)). Qed.
Lemma lem8054225 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (h1 : term52 _143007 _143008 _143009 f s) : term55 _143007 _143008 _143009 f s.
Proof. exact (fun h0 : term54 _143007 _143008 _143009 f s => @lem8054224 _143007 _143008 _143009 f s h1 h0). Qed.
Lemma lem8054226 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (h1 : term54 _143007 _143008 _143009 f s) : term54 _143007 _143008 _143009 f s.
Proof. exact (h1). Qed.
Lemma lem8054227 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (h1 : term52 _143007 _143008 _143009 f s) (h2 : term54 _143007 _143008 _143009 f s) : term52 _143007 _143008 _143009 f s.
Proof. exact (@lem8054225 _143007 _143008 _143009 f s h1 (@lem8054226 _143007 _143008 _143009 f s h2)). Qed.
Lemma lem8054228 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (h1 : term54 _143007 _143008 _143009 f s) : term54 _143007 _143008 _143009 f s.
Proof. exact (fun h0 : term52 _143007 _143008 _143009 f s => @lem8054227 _143007 _143008 _143009 f s h0 h1). Qed.
Lemma lem8054229 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : term56 _143007 _143008 _143009 f s.
Proof. exact (fun h0 : term54 _143007 _143008 _143009 f s => @lem8054228 _143007 _143008 _143009 f s h0). Qed.
Lemma lem8054232 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : term54 _143007 _143008 _143009 f s.
Proof. exact (@lem8054229 _143007 _143008 _143009 f s (@lem8054221 _143007 _143008 _143009 f s)). Qed.
Lemma lem8054233 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : term54 _143007 _143008 _143009 f s.
Proof. exact (@lem8054232 _143007 _143008 _143009 f s). Qed.
Lemma lem8054243 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8054244 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term52 _143007 _143008 _143009 f s) = (term57 _143007 _143008 _143009 f s).
Proof. exact (@lem8054243 (term53 _143007 _143008 _143009 f s)). Qed.
Lemma lem8054246 (t : Prop) : (term58 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8054247 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term57 _143007 _143008 _143009 f s) = (term50 _143007 _143008 _143009 f s).
Proof. exact (@lem8054246 (term50 _143007 _143008 _143009 f s)). Qed.
Lemma lem8054250 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term52 _143007 _143008 _143009 f s) = (term50 _143007 _143008 _143009 f s).
Proof. exact (TRANS (@lem8054244 _143007 _143008 _143009 f s) (@lem8054247 _143007 _143008 _143009 f s)). Qed.
Lemma lem8054279 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) : (term59 _143007 _143008 _143009 s) = (term60 _143007 _143008 _143009 s).
Proof. exact (fun_ext (fun f : type56 _143007 _143009 => @lem8054250 _143007 _143008 _143009 f s)). Qed.
Lemma lem8054280 {_143007 _143009 : Type'} : (@all (((cart _143007 _143009) -> Prop) -> Prop)) = (@all (((cart _143007 _143009) -> Prop) -> Prop)).
Proof. exact (eq_refl (@all (((cart _143007 _143009) -> Prop) -> Prop))). Qed.
Lemma lem8054281 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) : (term61 _143007 _143008 _143009 s) = (term62 _143007 _143008 _143009 s).
Proof. exact (MK_COMB (@lem8054280 _143007 _143009) (@lem8054279 _143007 _143008 _143009 s)). Qed.
Lemma lem8054286 {_143007 _143008 _143009 : Type'} : (term63 _143007 _143008 _143009) = (term64 _143007 _143008 _143009).
Proof. exact (fun_ext (fun s : type24 _143007 _143008 => @lem8054281 _143007 _143008 _143009 s)). Qed.
Lemma lem8054287 {_143007 _143008 : Type'} : (@all ((cart _143007 _143008) -> Prop)) = (@all ((cart _143007 _143008) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143007 _143008) -> Prop))). Qed.
Lemma lem8054296 {_143007 _143008 _143009 : Type'} : (term65 _143007 _143008 _143009) = (term66 _143007 _143008 _143009).
Proof. exact (MK_COMB (@lem8054287 _143007 _143008) (@lem8054286 _143007 _143008 _143009)). Qed.
Lemma lem8054305 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term38 _143007 _143008 _143009 f s x t y) = (term38 _143007 _143008 _143009 f s x t y).
Proof. exact (eq_refl (term38 _143007 _143008 _143009 f s x t y)). Qed.
Lemma lem8054306 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term40 _143007 _143008 _143009 f s x y) = (term40 _143007 _143008 _143009 f s x y).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8054305 _143007 _143008 _143009 f s x t y)). Qed.
Lemma lem8054307 {_143007 _143009 : Type'} : (@all ((cart _143007 _143009) -> Prop)) = (@all ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054308 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term42 _143007 _143008 _143009 f s x y) = (term42 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054307 _143007 _143009) (@lem8054306 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054313 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term27 _143007 _143009 f t y) = (term27 _143007 _143009 f t y).
Proof. exact (eq_refl (term27 _143007 _143009 f t y)). Qed.
Lemma lem8054314 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term29 _143007 _143009 f y) = (term29 _143007 _143009 f y).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8054313 _143007 _143009 f t y)). Qed.
Lemma lem8054315 {_143007 _143009 : Type'} : (@all ((cart _143007 _143009) -> Prop)) = (@all ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054316 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term30 _143007 _143009 f y) = (term30 _143007 _143009 f y).
Proof. exact (MK_COMB (@lem8054315 _143007 _143009) (@lem8054314 _143007 _143009 f y)). Qed.
Lemma lem8054319 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term19 _143007 _143008 s x) = (term19 _143007 _143008 s x).
Proof. exact (eq_refl (term19 _143007 _143008 s x)). Qed.
Lemma lem8054320 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term32 _143007 _143008 _143009 s x f y) = (term32 _143007 _143008 _143009 s x f y).
Proof. exact (MK_COMB (@lem8054319 _143007 _143008 s x) (@lem8054316 _143007 _143009 f y)). Qed.
Lemma lem8054321 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8054322 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term34 _143007 _143008 _143009 s x f y) = (term34 _143007 _143008 _143009 s x f y).
Proof. exact (MK_COMB (@lem8054321) (@lem8054320 _143007 _143008 _143009 s x f y)). Qed.
Lemma lem8054323 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : ((term32 _143007 _143008 _143009 s x f y) = (term42 _143007 _143008 _143009 f s x y)) = ((term32 _143007 _143008 _143009 s x f y) = (term42 _143007 _143008 _143009 f s x y)).
Proof. exact (MK_COMB (@lem8054322 _143007 _143008 _143009 s x f y) (@lem8054308 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054324 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term44 _143007 _143008 _143009 f s x) = (term44 _143007 _143008 _143009 f s x).
Proof. exact (fun_ext (fun y : cart _143007 _143009 => @lem8054323 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054325 {_143007 _143009 : Type'} : (@all (cart _143007 _143009)) = (@all (cart _143007 _143009)).
Proof. exact (eq_refl (@all (cart _143007 _143009))). Qed.
Lemma lem8054326 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term46 _143007 _143008 _143009 f s x) = (term46 _143007 _143008 _143009 f s x).
Proof. exact (MK_COMB (@lem8054325 _143007 _143009) (@lem8054324 _143007 _143008 _143009 f s x)). Qed.
Lemma lem8054327 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term48 _143007 _143008 _143009 f s) = (term48 _143007 _143008 _143009 f s).
Proof. exact (fun_ext (fun x : cart _143007 _143008 => @lem8054326 _143007 _143008 _143009 f s x)). Qed.
Lemma lem8054328 {_143007 _143008 : Type'} : (@all (cart _143007 _143008)) = (@all (cart _143007 _143008)).
Proof. exact (eq_refl (@all (cart _143007 _143008))). Qed.
Lemma lem8054329 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term49 _143007 _143008 _143009 f s) = (term49 _143007 _143008 _143009 f s).
Proof. exact (MK_COMB (@lem8054328 _143007 _143008) (@lem8054327 _143007 _143008 _143009 f s)). Qed.
Lemma lem8054332 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x : type24 _143007 _143009) : (term12 _143007 _143009 f x) = (term12 _143007 _143009 f x).
Proof. exact (eq_refl (term12 _143007 _143009 f x)). Qed.
Lemma lem8054333 {_143007 _143009 : Type'} (f : type56 _143007 _143009) : (term14 _143007 _143009 f) = (term14 _143007 _143009 f).
Proof. exact (fun_ext (fun x : type24 _143007 _143009 => @lem8054332 _143007 _143009 f x)). Qed.
Lemma lem8054334 {_143007 _143009 : Type'} : (@all ((cart _143007 _143009) -> Prop)) = (@all ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054335 {_143007 _143009 : Type'} (f : type56 _143007 _143009) : (term15 _143007 _143009 f) = (term15 _143007 _143009 f).
Proof. exact (MK_COMB (@lem8054334 _143007 _143009) (@lem8054333 _143007 _143009 f)). Qed.
Lemma lem8054336 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8054337 {_143007 _143009 : Type'} (f : type56 _143007 _143009) : (term16 _143007 _143009 f) = (term16 _143007 _143009 f).
Proof. exact (MK_COMB (@lem8054336) (@lem8054335 _143007 _143009 f)). Qed.
Lemma lem8054338 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8054339 {_143007 _143009 : Type'} (f : type56 _143007 _143009) : (term17 _143007 _143009 f) = (term17 _143007 _143009 f).
Proof. exact (MK_COMB (@lem8054338) (@lem8054337 _143007 _143009 f)). Qed.
Lemma lem8054340 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term50 _143007 _143008 _143009 f s) = (term50 _143007 _143008 _143009 f s).
Proof. exact (MK_COMB (@lem8054339 _143007 _143009 f) (@lem8054329 _143007 _143008 _143009 f s)). Qed.
Lemma lem8054341 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) : (term60 _143007 _143008 _143009 s) = (term60 _143007 _143008 _143009 s).
Proof. exact (fun_ext (fun f : type56 _143007 _143009 => @lem8054340 _143007 _143008 _143009 f s)). Qed.
Lemma lem8054342 {_143007 _143009 : Type'} : (@all (((cart _143007 _143009) -> Prop) -> Prop)) = (@all (((cart _143007 _143009) -> Prop) -> Prop)).
Proof. exact (eq_refl (@all (((cart _143007 _143009) -> Prop) -> Prop))). Qed.
Lemma lem8054343 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) : (term62 _143007 _143008 _143009 s) = (term62 _143007 _143008 _143009 s).
Proof. exact (MK_COMB (@lem8054342 _143007 _143009) (@lem8054341 _143007 _143008 _143009 s)). Qed.
Lemma lem8054344 {_143007 _143008 _143009 : Type'} : (term64 _143007 _143008 _143009) = (term64 _143007 _143008 _143009).
Proof. exact (fun_ext (fun s : type24 _143007 _143008 => @lem8054343 _143007 _143008 _143009 s)). Qed.
Lemma lem8054345 {_143007 _143008 : Type'} : (@all ((cart _143007 _143008) -> Prop)) = (@all ((cart _143007 _143008) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143007 _143008) -> Prop))). Qed.
Lemma lem8054346 {_143007 _143008 _143009 : Type'} : (term66 _143007 _143008 _143009) = (term66 _143007 _143008 _143009).
Proof. exact (MK_COMB (@lem8054345 _143007 _143008) (@lem8054344 _143007 _143008 _143009)). Qed.
Lemma lem8054401 {_143007 _143008 _143009 : Type'} : (term65 _143007 _143008 _143009) = (term66 _143007 _143008 _143009).
Proof. exact (TRANS (@lem8054296 _143007 _143008 _143009) (@lem8054346 _143007 _143008 _143009)). Qed.
Lemma lem8054402 {_143007 _143008 _143009 : Type'} : (term66 _143007 _143008 _143009) = (term65 _143007 _143008 _143009).
Proof. exact (SYM (@lem8054401 _143007 _143008 _143009)). Qed.
Lemma lem8054403 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (h1 : term16 _143007 _143009 f) : term16 _143007 _143009 f.
Proof. exact (h1). Qed.
Lemma lem8054405 (p : Prop) : p = (term51 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8054406 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : ((term32 _143007 _143008 _143009 s x f y) = (term42 _143007 _143008 _143009 f s x y)) = (term67 _143007 _143008 _143009 f s x y).
Proof. exact (@lem8054405 ((term32 _143007 _143008 _143009 s x f y) = (term42 _143007 _143008 _143009 f s x y))). Qed.
Lemma lem8054407 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term67 _143007 _143008 _143009 f s x y) = ((term32 _143007 _143008 _143009 s x f y) = (term42 _143007 _143008 _143009 f s x y)).
Proof. exact (SYM (@lem8054406 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054408 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term68 _143007 _143008 _143009 f s x y) : term68 _143007 _143008 _143009 f s x y.
Proof. exact (h1). Qed.
Lemma lem8054411 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x : type24 _143007 _143009) : (term69 _143007 _143009 f x) = (f x).
Proof. exact (@lem16933 (f x)). Qed.
Lemma lem8054412 {_143007 _143009 : Type'} (P : type56 _143007 _143009) : (term70 _143007 _143009 P) = (term71 _143007 _143009 P).
Proof. exact (@lem18392 (type24 _143007 _143009) P). Qed.
Lemma lem8054413 {_143007 _143009 : Type'} (f : type56 _143007 _143009) : (term16 _143007 _143009 f) = (term72 _143007 _143009 f).
Proof. exact (@lem8054412 _143007 _143009 (term14 _143007 _143009 f)). Qed.
Lemma lem8054414 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x : type24 _143007 _143009) : (term73 _143007 _143009 f x) = (term12 _143007 _143009 f x).
Proof. exact (eq_refl (term73 _143007 _143009 f x)). Qed.
Lemma lem8054415 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8054416 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x : type24 _143007 _143009) : (term74 _143007 _143009 f x) = (term69 _143007 _143009 f x).
Proof. exact (MK_COMB (@lem8054415) (@lem8054414 _143007 _143009 f x)). Qed.
Lemma lem8054417 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x : type24 _143007 _143009) : (term74 _143007 _143009 f x) = (f x).
Proof. exact (TRANS (@lem8054416 _143007 _143009 f x) (@lem8054411 _143007 _143009 f x)). Qed.
Lemma lem8054418 {_143007 _143009 : Type'} (f : type56 _143007 _143009) : (term75 _143007 _143009 f) = (term76 _143007 _143009 f).
Proof. exact (fun_ext (fun x : type24 _143007 _143009 => @lem8054417 _143007 _143009 f x)). Qed.
Lemma lem8054419 {_143007 _143009 : Type'} : (@ex ((cart _143007 _143009) -> Prop)) = (@ex ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054420 {_143007 _143009 : Type'} (f : type56 _143007 _143009) : (term72 _143007 _143009 f) = (term77 _143007 _143009 f).
Proof. exact (MK_COMB (@lem8054419 _143007 _143009) (@lem8054418 _143007 _143009 f)). Qed.
Lemma lem8054429 {_143007 _143009 : Type'} (f : type56 _143007 _143009) : (term16 _143007 _143009 f) = (term77 _143007 _143009 f).
Proof. exact (TRANS (@lem8054413 _143007 _143009 f) (@lem8054420 _143007 _143009 f)). Qed.
Lemma lem8054430 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (h1 : term16 _143007 _143009 f) : term77 _143007 _143009 f.
Proof. exact (EQ_MP (@lem8054429 _143007 _143009 f) (@lem8054403 _143007 _143009 f h1)). Qed.
Lemma lem8054441 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term78 _143007 _143009 f t y) = (term79 _143007 _143009 f t y).
Proof. exact (@lem17362 (f t) (t y)). Qed.
Lemma lem8054446 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term27 _143007 _143009 f t y) = (term80 _143007 _143009 f t y).
Proof. exact (@lem17265 (f t) (t y)). Qed.
Lemma lem8054447 {_143007 _143009 : Type'} (P : type56 _143007 _143009) : (term70 _143007 _143009 P) = (term71 _143007 _143009 P).
Proof. exact (@lem18392 (type24 _143007 _143009) P). Qed.
Lemma lem8054448 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term81 _143007 _143009 f y) = (term82 _143007 _143009 f y).
Proof. exact (@lem8054447 _143007 _143009 (term29 _143007 _143009 f y)). Qed.
Lemma lem8054449 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term83 _143007 _143009 f y t) = (term27 _143007 _143009 f t y).
Proof. exact (eq_refl (term83 _143007 _143009 f y t)). Qed.
Lemma lem8054450 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8054451 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term84 _143007 _143009 f y t) = (term78 _143007 _143009 f t y).
Proof. exact (MK_COMB (@lem8054450) (@lem8054449 _143007 _143009 f t y)). Qed.
Lemma lem8054452 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term84 _143007 _143009 f y t) = (term79 _143007 _143009 f t y).
Proof. exact (TRANS (@lem8054451 _143007 _143009 f t y) (@lem8054441 _143007 _143009 f t y)). Qed.
Lemma lem8054453 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term85 _143007 _143009 f y) = (term86 _143007 _143009 f y).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8054452 _143007 _143009 f t y)). Qed.
Lemma lem8054454 {_143007 _143009 : Type'} : (@ex ((cart _143007 _143009) -> Prop)) = (@ex ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054455 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term82 _143007 _143009 f y) = (term87 _143007 _143009 f y).
Proof. exact (MK_COMB (@lem8054454 _143007 _143009) (@lem8054453 _143007 _143009 f y)). Qed.
Lemma lem8054456 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term81 _143007 _143009 f y) = (term87 _143007 _143009 f y).
Proof. exact (TRANS (@lem8054448 _143007 _143009 f y) (@lem8054455 _143007 _143009 f y)). Qed.
Lemma lem8054457 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term29 _143007 _143009 f y) = (term88 _143007 _143009 f y).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8054446 _143007 _143009 f t y)). Qed.
Lemma lem8054458 {_143007 _143009 : Type'} : (@all ((cart _143007 _143009) -> Prop)) = (@all ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054459 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term30 _143007 _143009 f y) = (term89 _143007 _143009 f y).
Proof. exact (MK_COMB (@lem8054458 _143007 _143009) (@lem8054457 _143007 _143009 f y)). Qed.
Lemma lem8054461 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term90 _143007 _143008 s x) = (term90 _143007 _143008 s x).
Proof. exact (eq_refl (term90 _143007 _143008 s x)). Qed.
Lemma lem8054462 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term91 _143007 _143008 _143009 s x f y) = (term92 _143007 _143008 _143009 s x f y).
Proof. exact (MK_COMB (@lem8054461 _143007 _143008 s x) (@lem8054456 _143007 _143009 f y)). Qed.
Lemma lem8054463 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term93 _143007 _143008 _143009 s x f y) = (term91 _143007 _143008 _143009 s x f y).
Proof. exact (@lem17045 (s x) (term30 _143007 _143009 f y)). Qed.
Lemma lem8054464 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term93 _143007 _143008 _143009 s x f y) = (term92 _143007 _143008 _143009 s x f y).
Proof. exact (TRANS (@lem8054463 _143007 _143008 _143009 s x f y) (@lem8054462 _143007 _143008 _143009 s x f y)). Qed.
Lemma lem8054466 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term19 _143007 _143008 s x) = (term19 _143007 _143008 s x).
Proof. exact (eq_refl (term19 _143007 _143008 s x)). Qed.
Lemma lem8054467 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term32 _143007 _143008 _143009 s x f y) = (term94 _143007 _143008 _143009 s x f y).
Proof. exact (MK_COMB (@lem8054466 _143007 _143008 s x) (@lem8054459 _143007 _143009 f y)). Qed.
Lemma lem8054478 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term95 _143007 _143008 _143009 s x t y) = (term96 _143007 _143008 _143009 s x t y).
Proof. exact (@lem17045 (s x) (t y)). Qed.
Lemma lem8054483 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) : (term97 _143007 _143009 f t) = (term97 _143007 _143009 f t).
Proof. exact (eq_refl (term97 _143007 _143009 f t)). Qed.
Lemma lem8054484 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term98 _143007 _143008 _143009 f s x t y) = (term99 _143007 _143008 _143009 f s x t y).
Proof. exact (MK_COMB (@lem8054483 _143007 _143009 f t) (@lem8054478 _143007 _143008 _143009 s x t y)). Qed.
Lemma lem8054485 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term100 _143007 _143008 _143009 f s x t y) = (term98 _143007 _143008 _143009 f s x t y).
Proof. exact (@lem17362 (f t) (term36 _143007 _143008 _143009 s x t y)). Qed.
Lemma lem8054486 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term100 _143007 _143008 _143009 f s x t y) = (term99 _143007 _143008 _143009 f s x t y).
Proof. exact (TRANS (@lem8054485 _143007 _143008 _143009 f s x t y) (@lem8054484 _143007 _143008 _143009 f s x t y)). Qed.
Lemma lem8054491 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term38 _143007 _143008 _143009 f s x t y) = (term101 _143007 _143008 _143009 f s x t y).
Proof. exact (@lem17265 (f t) (term36 _143007 _143008 _143009 s x t y)). Qed.
Lemma lem8054492 {_143007 _143009 : Type'} (P : type56 _143007 _143009) : (term70 _143007 _143009 P) = (term71 _143007 _143009 P).
Proof. exact (@lem18392 (type24 _143007 _143009) P). Qed.
Lemma lem8054493 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term102 _143007 _143008 _143009 f s x y) = (term103 _143007 _143008 _143009 f s x y).
Proof. exact (@lem8054492 _143007 _143009 (term40 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054494 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term104 _143007 _143008 _143009 f s x y t) = (term38 _143007 _143008 _143009 f s x t y).
Proof. exact (eq_refl (term104 _143007 _143008 _143009 f s x y t)). Qed.
Lemma lem8054495 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8054496 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term105 _143007 _143008 _143009 f s x y t) = (term100 _143007 _143008 _143009 f s x t y).
Proof. exact (MK_COMB (@lem8054495) (@lem8054494 _143007 _143008 _143009 f s x t y)). Qed.
Lemma lem8054497 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term105 _143007 _143008 _143009 f s x y t) = (term99 _143007 _143008 _143009 f s x t y).
Proof. exact (TRANS (@lem8054496 _143007 _143008 _143009 f s x t y) (@lem8054486 _143007 _143008 _143009 f s x t y)). Qed.
Lemma lem8054498 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term106 _143007 _143008 _143009 f s x y) = (term107 _143007 _143008 _143009 f s x y).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8054497 _143007 _143008 _143009 f s x t y)). Qed.
Lemma lem8054499 {_143007 _143009 : Type'} : (@ex ((cart _143007 _143009) -> Prop)) = (@ex ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054500 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term103 _143007 _143008 _143009 f s x y) = (term108 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054499 _143007 _143009) (@lem8054498 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054501 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term102 _143007 _143008 _143009 f s x y) = (term108 _143007 _143008 _143009 f s x y).
Proof. exact (TRANS (@lem8054493 _143007 _143008 _143009 f s x y) (@lem8054500 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054502 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term40 _143007 _143008 _143009 f s x y) = (term109 _143007 _143008 _143009 f s x y).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8054491 _143007 _143008 _143009 f s x t y)). Qed.
Lemma lem8054503 {_143007 _143009 : Type'} : (@all ((cart _143007 _143009) -> Prop)) = (@all ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054504 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term42 _143007 _143008 _143009 f s x y) = (term110 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054503 _143007 _143009) (@lem8054502 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054505 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8054506 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term111 _143007 _143008 _143009 s x f y) = (term112 _143007 _143008 _143009 s x f y).
Proof. exact (MK_COMB (@lem8054505) (@lem8054464 _143007 _143008 _143009 s x f y)). Qed.
Lemma lem8054507 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term113 _143007 _143008 _143009 f s x y) = (term114 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054506 _143007 _143008 _143009 s x f y) (@lem8054504 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054508 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8054509 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term115 _143007 _143008 _143009 s x f y) = (term116 _143007 _143008 _143009 s x f y).
Proof. exact (MK_COMB (@lem8054508) (@lem8054467 _143007 _143008 _143009 s x f y)). Qed.
Lemma lem8054510 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term117 _143007 _143008 _143009 f s x y) = (term118 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054509 _143007 _143008 _143009 s x f y) (@lem8054501 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054511 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8054512 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term119 _143007 _143008 _143009 f s x y) = (term120 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054511) (@lem8054510 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054513 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term121 _143007 _143008 _143009 f s x y) = (term122 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054512 _143007 _143008 _143009 f s x y) (@lem8054507 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054514 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term68 _143007 _143008 _143009 f s x y) = (term121 _143007 _143008 _143009 f s x y).
Proof. exact (@lem17646 (term32 _143007 _143008 _143009 s x f y) (term42 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054515 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term68 _143007 _143008 _143009 f s x y) = (term122 _143007 _143008 _143009 f s x y).
Proof. exact (TRANS (@lem8054514 _143007 _143008 _143009 f s x y) (@lem8054513 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054670 {A : Type'} (P : Prop) (Q : A -> Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8054671 {_143007 _143009 : Type'} (P : Prop) (Q : type56 _143007 _143009) : (term125 _143007 _143009 P Q) = (term126 _143007 _143009 P Q).
Proof. exact (@lem8054670 (type24 _143007 _143009) P Q). Qed.
Lemma lem8054672 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term127 _143007 _143008 _143009 f s x y) = (term128 _143007 _143008 _143009 f s x y).
Proof. exact (@lem8054671 _143007 _143009 (term94 _143007 _143008 _143009 s x f y) (term107 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054673 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term129 _143007 _143008 _143009 f s x y t) = (term99 _143007 _143008 _143009 f s x t y).
Proof. exact (eq_refl (term129 _143007 _143008 _143009 f s x y t)). Qed.
Lemma lem8054674 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term130 _143007 _143008 _143009 f s x y) = (term107 _143007 _143008 _143009 f s x y).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8054673 _143007 _143008 _143009 f s x t y)). Qed.
Lemma lem8054675 {_143007 _143009 : Type'} : (@ex ((cart _143007 _143009) -> Prop)) = (@ex ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054676 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term131 _143007 _143008 _143009 f s x y) = (term108 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054675 _143007 _143009) (@lem8054674 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054677 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term116 _143007 _143008 _143009 s x f y) = (term116 _143007 _143008 _143009 s x f y).
Proof. exact (eq_refl (term116 _143007 _143008 _143009 s x f y)). Qed.
Lemma lem8054678 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term127 _143007 _143008 _143009 f s x y) = (term118 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054677 _143007 _143008 _143009 s x f y) (@lem8054676 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054679 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8054680 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term132 _143007 _143008 _143009 f s x y) = (term133 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054679) (@lem8054678 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054681 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term129 _143007 _143008 _143009 f s x y t) = (term99 _143007 _143008 _143009 f s x t y).
Proof. exact (eq_refl (term129 _143007 _143008 _143009 f s x y t)). Qed.
Lemma lem8054682 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term116 _143007 _143008 _143009 s x f y) = (term116 _143007 _143008 _143009 s x f y).
Proof. exact (eq_refl (term116 _143007 _143008 _143009 s x f y)). Qed.
Lemma lem8054683 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term134 _143007 _143008 _143009 f s x y t) = (term135 _143007 _143008 _143009 f s x t y).
Proof. exact (MK_COMB (@lem8054682 _143007 _143008 _143009 s x f y) (@lem8054681 _143007 _143008 _143009 f s x t y)). Qed.
Lemma lem8054684 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term136 _143007 _143008 _143009 f s x y) = (term137 _143007 _143008 _143009 f s x y).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8054683 _143007 _143008 _143009 f s x t y)). Qed.
Lemma lem8054685 {_143007 _143009 : Type'} : (@ex ((cart _143007 _143009) -> Prop)) = (@ex ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054686 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term128 _143007 _143008 _143009 f s x y) = (term138 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054685 _143007 _143009) (@lem8054684 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054687 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : ((term127 _143007 _143008 _143009 f s x y) = (term128 _143007 _143008 _143009 f s x y)) = ((term118 _143007 _143008 _143009 f s x y) = (term138 _143007 _143008 _143009 f s x y)).
Proof. exact (MK_COMB (@lem8054680 _143007 _143008 _143009 f s x y) (@lem8054686 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054688 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term118 _143007 _143008 _143009 f s x y) = (term138 _143007 _143008 _143009 f s x y).
Proof. exact (EQ_MP (@lem8054687 _143007 _143008 _143009 f s x y) (@lem8054672 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054689 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8054690 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term120 _143007 _143008 _143009 f s x y) = (term139 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054689) (@lem8054688 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054692 {A : Type'} (P : Prop) (Q : A -> Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8054693 {_143007 _143009 : Type'} (P : Prop) (Q : type56 _143007 _143009) : (term142 _143007 _143009 P Q) = (term143 _143007 _143009 P Q).
Proof. exact (@lem8054692 (type24 _143007 _143009) P Q). Qed.
Lemma lem8054694 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term144 _143007 _143008 _143009 s x f y) = (term145 _143007 _143008 _143009 s x f y).
Proof. exact (@lem8054693 _143007 _143009 (term146 _143007 _143008 s x) (term86 _143007 _143009 f y)). Qed.
Lemma lem8054695 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term147 _143007 _143009 f y t) = (term79 _143007 _143009 f t y).
Proof. exact (eq_refl (term147 _143007 _143009 f y t)). Qed.
Lemma lem8054696 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term148 _143007 _143009 f y) = (term86 _143007 _143009 f y).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8054695 _143007 _143009 f t y)). Qed.
Lemma lem8054697 {_143007 _143009 : Type'} : (@ex ((cart _143007 _143009) -> Prop)) = (@ex ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054698 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term149 _143007 _143009 f y) = (term87 _143007 _143009 f y).
Proof. exact (MK_COMB (@lem8054697 _143007 _143009) (@lem8054696 _143007 _143009 f y)). Qed.
Lemma lem8054699 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term90 _143007 _143008 s x) = (term90 _143007 _143008 s x).
Proof. exact (eq_refl (term90 _143007 _143008 s x)). Qed.
Lemma lem8054700 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term144 _143007 _143008 _143009 s x f y) = (term92 _143007 _143008 _143009 s x f y).
Proof. exact (MK_COMB (@lem8054699 _143007 _143008 s x) (@lem8054698 _143007 _143009 f y)). Qed.
Lemma lem8054701 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8054702 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term150 _143007 _143008 _143009 s x f y) = (term151 _143007 _143008 _143009 s x f y).
Proof. exact (MK_COMB (@lem8054701) (@lem8054700 _143007 _143008 _143009 s x f y)). Qed.
Lemma lem8054703 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term147 _143007 _143009 f y t) = (term79 _143007 _143009 f t y).
Proof. exact (eq_refl (term147 _143007 _143009 f y t)). Qed.
Lemma lem8054704 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term90 _143007 _143008 s x) = (term90 _143007 _143008 s x).
Proof. exact (eq_refl (term90 _143007 _143008 s x)). Qed.
Lemma lem8054705 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term152 _143007 _143008 _143009 s x f y t) = (term153 _143007 _143008 _143009 s x f t y).
Proof. exact (MK_COMB (@lem8054704 _143007 _143008 s x) (@lem8054703 _143007 _143009 f t y)). Qed.
Lemma lem8054706 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term154 _143007 _143008 _143009 s x f y) = (term155 _143007 _143008 _143009 s x f y).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8054705 _143007 _143008 _143009 s x f t y)). Qed.
Lemma lem8054707 {_143007 _143009 : Type'} : (@ex ((cart _143007 _143009) -> Prop)) = (@ex ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054708 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term145 _143007 _143008 _143009 s x f y) = (term156 _143007 _143008 _143009 s x f y).
Proof. exact (MK_COMB (@lem8054707 _143007 _143009) (@lem8054706 _143007 _143008 _143009 s x f y)). Qed.
Lemma lem8054709 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : ((term144 _143007 _143008 _143009 s x f y) = (term145 _143007 _143008 _143009 s x f y)) = ((term92 _143007 _143008 _143009 s x f y) = (term156 _143007 _143008 _143009 s x f y)).
Proof. exact (MK_COMB (@lem8054702 _143007 _143008 _143009 s x f y) (@lem8054708 _143007 _143008 _143009 s x f y)). Qed.
Lemma lem8054710 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term92 _143007 _143008 _143009 s x f y) = (term156 _143007 _143008 _143009 s x f y).
Proof. exact (EQ_MP (@lem8054709 _143007 _143008 _143009 s x f y) (@lem8054694 _143007 _143008 _143009 s x f y)). Qed.
Lemma lem8054711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8054712 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term112 _143007 _143008 _143009 s x f y) = (term157 _143007 _143008 _143009 s x f y).
Proof. exact (MK_COMB (@lem8054711) (@lem8054710 _143007 _143008 _143009 s x f y)). Qed.
Lemma lem8054713 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term110 _143007 _143008 _143009 f s x y) = (term110 _143007 _143008 _143009 f s x y).
Proof. exact (eq_refl (term110 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054714 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term114 _143007 _143008 _143009 f s x y) = (term158 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054712 _143007 _143008 _143009 s x f y) (@lem8054713 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054716 {A : Type'} (P : A -> Prop) (Q : Prop) : (term159 A P Q) = (term160 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8054717 {_143007 _143009 : Type'} (P : type56 _143007 _143009) (Q : Prop) : (term161 _143007 _143009 P Q) = (term162 _143007 _143009 P Q).
Proof. exact (@lem8054716 (type24 _143007 _143009) P Q). Qed.
Lemma lem8054718 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term163 _143007 _143008 _143009 f s x y) = (term164 _143007 _143008 _143009 f s x y).
Proof. exact (@lem8054717 _143007 _143009 (term155 _143007 _143008 _143009 s x f y) (term110 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054719 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term165 _143007 _143008 _143009 s x f y t) = (term153 _143007 _143008 _143009 s x f t y).
Proof. exact (eq_refl (term165 _143007 _143008 _143009 s x f y t)). Qed.
Lemma lem8054720 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term166 _143007 _143008 _143009 s x f y) = (term155 _143007 _143008 _143009 s x f y).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8054719 _143007 _143008 _143009 s x f t y)). Qed.
Lemma lem8054721 {_143007 _143009 : Type'} : (@ex ((cart _143007 _143009) -> Prop)) = (@ex ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054722 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term167 _143007 _143008 _143009 s x f y) = (term156 _143007 _143008 _143009 s x f y).
Proof. exact (MK_COMB (@lem8054721 _143007 _143009) (@lem8054720 _143007 _143008 _143009 s x f y)). Qed.
Lemma lem8054723 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8054724 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term168 _143007 _143008 _143009 s x f y) = (term157 _143007 _143008 _143009 s x f y).
Proof. exact (MK_COMB (@lem8054723) (@lem8054722 _143007 _143008 _143009 s x f y)). Qed.
Lemma lem8054725 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term110 _143007 _143008 _143009 f s x y) = (term110 _143007 _143008 _143009 f s x y).
Proof. exact (eq_refl (term110 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054726 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term163 _143007 _143008 _143009 f s x y) = (term158 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054724 _143007 _143008 _143009 s x f y) (@lem8054725 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054727 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8054728 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term169 _143007 _143008 _143009 f s x y) = (term170 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054727) (@lem8054726 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054729 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term165 _143007 _143008 _143009 s x f y t) = (term153 _143007 _143008 _143009 s x f t y).
Proof. exact (eq_refl (term165 _143007 _143008 _143009 s x f y t)). Qed.
Lemma lem8054730 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8054731 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term171 _143007 _143008 _143009 s x f y t) = (term172 _143007 _143008 _143009 s x f t y).
Proof. exact (MK_COMB (@lem8054730) (@lem8054729 _143007 _143008 _143009 s x f t y)). Qed.
Lemma lem8054732 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term110 _143007 _143008 _143009 f s x y) = (term110 _143007 _143008 _143009 f s x y).
Proof. exact (eq_refl (term110 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054733 {_143007 _143008 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term173 _143007 _143008 _143009 t f s x y) = (term174 _143007 _143008 _143009 t f s x y).
Proof. exact (MK_COMB (@lem8054731 _143007 _143008 _143009 s x f t y) (@lem8054732 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054734 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term175 _143007 _143008 _143009 f s x y) = (term176 _143007 _143008 _143009 f s x y).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8054733 _143007 _143008 _143009 t f s x y)). Qed.
Lemma lem8054735 {_143007 _143009 : Type'} : (@ex ((cart _143007 _143009) -> Prop)) = (@ex ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054736 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term164 _143007 _143008 _143009 f s x y) = (term177 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054735 _143007 _143009) (@lem8054734 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054737 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : ((term163 _143007 _143008 _143009 f s x y) = (term164 _143007 _143008 _143009 f s x y)) = ((term158 _143007 _143008 _143009 f s x y) = (term177 _143007 _143008 _143009 f s x y)).
Proof. exact (MK_COMB (@lem8054728 _143007 _143008 _143009 f s x y) (@lem8054736 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054738 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term158 _143007 _143008 _143009 f s x y) = (term177 _143007 _143008 _143009 f s x y).
Proof. exact (EQ_MP (@lem8054737 _143007 _143008 _143009 f s x y) (@lem8054718 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054739 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term114 _143007 _143008 _143009 f s x y) = (term177 _143007 _143008 _143009 f s x y).
Proof. exact (TRANS (@lem8054714 _143007 _143008 _143009 f s x y) (@lem8054738 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054740 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term122 _143007 _143008 _143009 f s x y) = (term178 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054690 _143007 _143008 _143009 f s x y) (@lem8054739 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054742 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem8054743 {_143007 _143009 : Type'} (P : type56 _143007 _143009) (Q : type56 _143007 _143009) : (term181 _143007 _143009 P Q) = (term182 _143007 _143009 P Q).
Proof. exact (@lem8054742 (type24 _143007 _143009) P Q). Qed.
Lemma lem8054744 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term183 _143007 _143008 _143009 f s x y) = (term184 _143007 _143008 _143009 f s x y).
Proof. exact (@lem8054743 _143007 _143009 (term137 _143007 _143008 _143009 f s x y) (term176 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054745 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term185 _143007 _143008 _143009 f s x y t) = (term135 _143007 _143008 _143009 f s x t y).
Proof. exact (eq_refl (term185 _143007 _143008 _143009 f s x y t)). Qed.
Lemma lem8054746 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term186 _143007 _143008 _143009 f s x y) = (term137 _143007 _143008 _143009 f s x y).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8054745 _143007 _143008 _143009 f s x t y)). Qed.
Lemma lem8054747 {_143007 _143009 : Type'} : (@ex ((cart _143007 _143009) -> Prop)) = (@ex ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054748 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term187 _143007 _143008 _143009 f s x y) = (term138 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054747 _143007 _143009) (@lem8054746 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054749 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8054750 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term188 _143007 _143008 _143009 f s x y) = (term139 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054749) (@lem8054748 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054751 {_143007 _143008 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term189 _143007 _143008 _143009 f s x y t) = (term174 _143007 _143008 _143009 t f s x y).
Proof. exact (eq_refl (term189 _143007 _143008 _143009 f s x y t)). Qed.
Lemma lem8054752 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term190 _143007 _143008 _143009 f s x y) = (term176 _143007 _143008 _143009 f s x y).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8054751 _143007 _143008 _143009 t f s x y)). Qed.
Lemma lem8054753 {_143007 _143009 : Type'} : (@ex ((cart _143007 _143009) -> Prop)) = (@ex ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054754 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term191 _143007 _143008 _143009 f s x y) = (term177 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054753 _143007 _143009) (@lem8054752 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054755 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term183 _143007 _143008 _143009 f s x y) = (term178 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054750 _143007 _143008 _143009 f s x y) (@lem8054754 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054756 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8054757 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term192 _143007 _143008 _143009 f s x y) = (term193 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054756) (@lem8054755 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054758 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term185 _143007 _143008 _143009 f s x y t) = (term135 _143007 _143008 _143009 f s x t y).
Proof. exact (eq_refl (term185 _143007 _143008 _143009 f s x y t)). Qed.
Lemma lem8054759 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8054760 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term194 _143007 _143008 _143009 f s x y t) = (term195 _143007 _143008 _143009 f s x t y).
Proof. exact (MK_COMB (@lem8054759) (@lem8054758 _143007 _143008 _143009 f s x t y)). Qed.
Lemma lem8054761 {_143007 _143008 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term189 _143007 _143008 _143009 f s x y t) = (term174 _143007 _143008 _143009 t f s x y).
Proof. exact (eq_refl (term189 _143007 _143008 _143009 f s x y t)). Qed.
Lemma lem8054762 {_143007 _143008 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term196 _143007 _143008 _143009 f s x y t) = (term197 _143007 _143008 _143009 t f s x y).
Proof. exact (MK_COMB (@lem8054760 _143007 _143008 _143009 f s x t y) (@lem8054761 _143007 _143008 _143009 t f s x y)). Qed.
Lemma lem8054763 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term198 _143007 _143008 _143009 f s x y) = (term199 _143007 _143008 _143009 f s x y).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8054762 _143007 _143008 _143009 t f s x y)). Qed.
Lemma lem8054764 {_143007 _143009 : Type'} : (@ex ((cart _143007 _143009) -> Prop)) = (@ex ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054765 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term184 _143007 _143008 _143009 f s x y) = (term200 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054764 _143007 _143009) (@lem8054763 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054766 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : ((term183 _143007 _143008 _143009 f s x y) = (term184 _143007 _143008 _143009 f s x y)) = ((term178 _143007 _143008 _143009 f s x y) = (term200 _143007 _143008 _143009 f s x y)).
Proof. exact (MK_COMB (@lem8054757 _143007 _143008 _143009 f s x y) (@lem8054765 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054767 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term178 _143007 _143008 _143009 f s x y) = (term200 _143007 _143008 _143009 f s x y).
Proof. exact (EQ_MP (@lem8054766 _143007 _143008 _143009 f s x y) (@lem8054744 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054769 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term122 _143007 _143008 _143009 f s x y) = (term200 _143007 _143008 _143009 f s x y).
Proof. exact (TRANS (@lem8054740 _143007 _143008 _143009 f s x y) (@lem8054767 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054770 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term68 _143007 _143008 _143009 f s x y) = (term200 _143007 _143008 _143009 f s x y).
Proof. exact (TRANS (@lem8054515 _143007 _143008 _143009 f s x y) (@lem8054769 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054771 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term68 _143007 _143008 _143009 f s x y) : term200 _143007 _143008 _143009 f s x y.
Proof. exact (EQ_MP (@lem8054770 _143007 _143008 _143009 f s x y) (@lem8054408 _143007 _143008 _143009 f s x y h1)). Qed.
Lemma lem8054772 {_143007 _143008 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term197 _143007 _143008 _143009 t f s x y) : term197 _143007 _143008 _143009 t f s x y.
Proof. exact (h1). Qed.
Lemma lem8054773 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x' : type24 _143007 _143009) (h1 : f x') : f x'.
Proof. exact (h1). Qed.
Lemma lem8054778 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8054779 {_143007 _143009 : Type'} (f : type24 _143007 _143009) (x : cart _143007 _143009) : (f x) = (@I ((cart _143007 _143009) -> Prop) f x).
Proof. exact (@lem8054778 (cart _143007 _143009) Prop f x). Qed.
Lemma lem8054781 {_143007 _143009 : Type'} (t : type24 _143007 _143009) (y : cart _143007 _143009) : (t y) = (@I ((cart _143007 _143009) -> Prop) t y).
Proof. exact (@lem8054779 _143007 _143009 t y). Qed.
Lemma lem8054786 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8054787 {_143007 _143008 : Type'} (f : type24 _143007 _143008) (x : cart _143007 _143008) : (f x) = (@I ((cart _143007 _143008) -> Prop) f x).
Proof. exact (@lem8054786 (cart _143007 _143008) Prop f x). Qed.
Lemma lem8054789 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (s x) = (@I ((cart _143007 _143008) -> Prop) s x).
Proof. exact (@lem8054787 _143007 _143008 s x). Qed.
Lemma lem8054790 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8054791 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term19 _143007 _143008 s x) = (term201 _143007 _143008 s x).
Proof. exact (MK_COMB (@lem8054790) (@lem8054789 _143007 _143008 s x)). Qed.
Lemma lem8054792 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term36 _143007 _143008 _143009 s x t y) = (term202 _143007 _143008 _143009 s x t y).
Proof. exact (MK_COMB (@lem8054791 _143007 _143008 s x) (@lem8054781 _143007 _143009 t y)). Qed.
Lemma lem8054793 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8054798 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8054799 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x : type24 _143007 _143009) : (f x) = (@I (((cart _143007 _143009) -> Prop) -> Prop) f x).
Proof. exact (@lem8054798 (type24 _143007 _143009) Prop f x). Qed.
Lemma lem8054801 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) : (f t) = (@I (((cart _143007 _143009) -> Prop) -> Prop) f t).
Proof. exact (@lem8054799 _143007 _143009 f t). Qed.
Lemma lem8054802 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) : (term12 _143007 _143009 f t) = (term203 _143007 _143009 f t).
Proof. exact (MK_COMB (@lem8054793) (@lem8054801 _143007 _143009 f t)). Qed.
Lemma lem8054803 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8054804 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) : (term204 _143007 _143009 f t) = (term205 _143007 _143009 f t).
Proof. exact (MK_COMB (@lem8054803) (@lem8054802 _143007 _143009 f t)). Qed.
Lemma lem8054805 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term101 _143007 _143008 _143009 f s x t y) = (term206 _143007 _143008 _143009 f s x t y).
Proof. exact (MK_COMB (@lem8054804 _143007 _143009 f t) (@lem8054792 _143007 _143008 _143009 s x t y)). Qed.
Lemma lem8054806 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term109 _143007 _143008 _143009 f s x y) = (term207 _143007 _143008 _143009 f s x y).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8054805 _143007 _143008 _143009 f s x t y)). Qed.
Lemma lem8054807 {_143007 _143009 : Type'} : (@all ((cart _143007 _143009) -> Prop)) = (@all ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054808 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term110 _143007 _143008 _143009 f s x y) = (term208 _143007 _143008 _143009 f s x y).
Proof. exact (MK_COMB (@lem8054807 _143007 _143009) (@lem8054806 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054809 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8054814 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8054815 {_143007 _143009 : Type'} (f : type24 _143007 _143009) (x : cart _143007 _143009) : (f x) = (@I ((cart _143007 _143009) -> Prop) f x).
Proof. exact (@lem8054814 (cart _143007 _143009) Prop f x). Qed.
Lemma lem8054817 {_143007 _143009 : Type'} (t : type24 _143007 _143009) (y : cart _143007 _143009) : (t y) = (@I ((cart _143007 _143009) -> Prop) t y).
Proof. exact (@lem8054815 _143007 _143009 t y). Qed.
Lemma lem8054818 {_143007 _143009 : Type'} (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term146 _143007 _143009 t y) = (term209 _143007 _143009 t y).
Proof. exact (MK_COMB (@lem8054809) (@lem8054817 _143007 _143009 t y)). Qed.
Lemma lem8054823 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8054824 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x : type24 _143007 _143009) : (f x) = (@I (((cart _143007 _143009) -> Prop) -> Prop) f x).
Proof. exact (@lem8054823 (type24 _143007 _143009) Prop f x). Qed.
Lemma lem8054826 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) : (f t) = (@I (((cart _143007 _143009) -> Prop) -> Prop) f t).
Proof. exact (@lem8054824 _143007 _143009 f t). Qed.
Lemma lem8054827 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8054828 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) : (term97 _143007 _143009 f t) = (term210 _143007 _143009 f t).
Proof. exact (MK_COMB (@lem8054827) (@lem8054826 _143007 _143009 f t)). Qed.
Lemma lem8054829 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term79 _143007 _143009 f t y) = (term211 _143007 _143009 f t y).
Proof. exact (MK_COMB (@lem8054828 _143007 _143009 f t) (@lem8054818 _143007 _143009 t y)). Qed.
Lemma lem8054830 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8054835 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8054836 {_143007 _143008 : Type'} (f : type24 _143007 _143008) (x : cart _143007 _143008) : (f x) = (@I ((cart _143007 _143008) -> Prop) f x).
Proof. exact (@lem8054835 (cart _143007 _143008) Prop f x). Qed.
Lemma lem8054838 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (s x) = (@I ((cart _143007 _143008) -> Prop) s x).
Proof. exact (@lem8054836 _143007 _143008 s x). Qed.
Lemma lem8054839 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term146 _143007 _143008 s x) = (term209 _143007 _143008 s x).
Proof. exact (MK_COMB (@lem8054830) (@lem8054838 _143007 _143008 s x)). Qed.
Lemma lem8054840 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8054841 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term90 _143007 _143008 s x) = (term212 _143007 _143008 s x).
Proof. exact (MK_COMB (@lem8054840) (@lem8054839 _143007 _143008 s x)). Qed.
Lemma lem8054842 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term153 _143007 _143008 _143009 s x f t y) = (term213 _143007 _143008 _143009 s x f t y).
Proof. exact (MK_COMB (@lem8054841 _143007 _143008 s x) (@lem8054829 _143007 _143009 f t y)). Qed.
Lemma lem8054843 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8054844 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term172 _143007 _143008 _143009 s x f t y) = (term214 _143007 _143008 _143009 s x f t y).
Proof. exact (MK_COMB (@lem8054843) (@lem8054842 _143007 _143008 _143009 s x f t y)). Qed.
Lemma lem8054845 {_143007 _143008 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term174 _143007 _143008 _143009 t f s x y) = (term215 _143007 _143008 _143009 t f s x y).
Proof. exact (MK_COMB (@lem8054844 _143007 _143008 _143009 s x f t y) (@lem8054808 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8054846 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8054851 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8054852 {_143007 _143009 : Type'} (f : type24 _143007 _143009) (x : cart _143007 _143009) : (f x) = (@I ((cart _143007 _143009) -> Prop) f x).
Proof. exact (@lem8054851 (cart _143007 _143009) Prop f x). Qed.
Lemma lem8054854 {_143007 _143009 : Type'} (t : type24 _143007 _143009) (y : cart _143007 _143009) : (t y) = (@I ((cart _143007 _143009) -> Prop) t y).
Proof. exact (@lem8054852 _143007 _143009 t y). Qed.
Lemma lem8054855 {_143007 _143009 : Type'} (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term146 _143007 _143009 t y) = (term209 _143007 _143009 t y).
Proof. exact (MK_COMB (@lem8054846) (@lem8054854 _143007 _143009 t y)). Qed.
Lemma lem8054856 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8054861 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8054862 {_143007 _143008 : Type'} (f : type24 _143007 _143008) (x : cart _143007 _143008) : (f x) = (@I ((cart _143007 _143008) -> Prop) f x).
Proof. exact (@lem8054861 (cart _143007 _143008) Prop f x). Qed.
Lemma lem8054864 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (s x) = (@I ((cart _143007 _143008) -> Prop) s x).
Proof. exact (@lem8054862 _143007 _143008 s x). Qed.
Lemma lem8054865 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term146 _143007 _143008 s x) = (term209 _143007 _143008 s x).
Proof. exact (MK_COMB (@lem8054856) (@lem8054864 _143007 _143008 s x)). Qed.
Lemma lem8054866 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8054867 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term90 _143007 _143008 s x) = (term212 _143007 _143008 s x).
Proof. exact (MK_COMB (@lem8054866) (@lem8054865 _143007 _143008 s x)). Qed.
Lemma lem8054868 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term96 _143007 _143008 _143009 s x t y) = (term216 _143007 _143008 _143009 s x t y).
Proof. exact (MK_COMB (@lem8054867 _143007 _143008 s x) (@lem8054855 _143007 _143009 t y)). Qed.
Lemma lem8054873 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8054874 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x : type24 _143007 _143009) : (f x) = (@I (((cart _143007 _143009) -> Prop) -> Prop) f x).
Proof. exact (@lem8054873 (type24 _143007 _143009) Prop f x). Qed.
Lemma lem8054876 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) : (f t) = (@I (((cart _143007 _143009) -> Prop) -> Prop) f t).
Proof. exact (@lem8054874 _143007 _143009 f t). Qed.
Lemma lem8054877 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8054878 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) : (term97 _143007 _143009 f t) = (term210 _143007 _143009 f t).
Proof. exact (MK_COMB (@lem8054877) (@lem8054876 _143007 _143009 f t)). Qed.
Lemma lem8054879 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term99 _143007 _143008 _143009 f s x t y) = (term217 _143007 _143008 _143009 f s x t y).
Proof. exact (MK_COMB (@lem8054878 _143007 _143009 f t) (@lem8054868 _143007 _143008 _143009 s x t y)). Qed.
Lemma lem8054884 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8054885 {_143007 _143009 : Type'} (f : type24 _143007 _143009) (x : cart _143007 _143009) : (f x) = (@I ((cart _143007 _143009) -> Prop) f x).
Proof. exact (@lem8054884 (cart _143007 _143009) Prop f x). Qed.
Lemma lem8054887 {_143007 _143009 : Type'} (t : type24 _143007 _143009) (y : cart _143007 _143009) : (t y) = (@I ((cart _143007 _143009) -> Prop) t y).
Proof. exact (@lem8054885 _143007 _143009 t y). Qed.
Lemma lem8054888 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8054893 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8054894 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x : type24 _143007 _143009) : (f x) = (@I (((cart _143007 _143009) -> Prop) -> Prop) f x).
Proof. exact (@lem8054893 (type24 _143007 _143009) Prop f x). Qed.
Lemma lem8054896 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) : (f t) = (@I (((cart _143007 _143009) -> Prop) -> Prop) f t).
Proof. exact (@lem8054894 _143007 _143009 f t). Qed.
Lemma lem8054897 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) : (term12 _143007 _143009 f t) = (term203 _143007 _143009 f t).
Proof. exact (MK_COMB (@lem8054888) (@lem8054896 _143007 _143009 f t)). Qed.
Lemma lem8054898 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8054899 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) : (term204 _143007 _143009 f t) = (term205 _143007 _143009 f t).
Proof. exact (MK_COMB (@lem8054898) (@lem8054897 _143007 _143009 f t)). Qed.
Lemma lem8054900 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term80 _143007 _143009 f t y) = (term218 _143007 _143009 f t y).
Proof. exact (MK_COMB (@lem8054899 _143007 _143009 f t) (@lem8054887 _143007 _143009 t y)). Qed.
Lemma lem8054901 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term88 _143007 _143009 f y) = (term219 _143007 _143009 f y).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8054900 _143007 _143009 f t y)). Qed.
Lemma lem8054902 {_143007 _143009 : Type'} : (@all ((cart _143007 _143009) -> Prop)) = (@all ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054903 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term89 _143007 _143009 f y) = (term220 _143007 _143009 f y).
Proof. exact (MK_COMB (@lem8054902 _143007 _143009) (@lem8054901 _143007 _143009 f y)). Qed.
Lemma lem8054908 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8054909 {_143007 _143008 : Type'} (f : type24 _143007 _143008) (x : cart _143007 _143008) : (f x) = (@I ((cart _143007 _143008) -> Prop) f x).
Proof. exact (@lem8054908 (cart _143007 _143008) Prop f x). Qed.
Lemma lem8054911 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (s x) = (@I ((cart _143007 _143008) -> Prop) s x).
Proof. exact (@lem8054909 _143007 _143008 s x). Qed.
Lemma lem8054912 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8054913 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term19 _143007 _143008 s x) = (term201 _143007 _143008 s x).
Proof. exact (MK_COMB (@lem8054912) (@lem8054911 _143007 _143008 s x)). Qed.
Lemma lem8054914 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term94 _143007 _143008 _143009 s x f y) = (term221 _143007 _143008 _143009 s x f y).
Proof. exact (MK_COMB (@lem8054913 _143007 _143008 s x) (@lem8054903 _143007 _143009 f y)). Qed.
Lemma lem8054915 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8054916 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term116 _143007 _143008 _143009 s x f y) = (term222 _143007 _143008 _143009 s x f y).
Proof. exact (MK_COMB (@lem8054915) (@lem8054914 _143007 _143008 _143009 s x f y)). Qed.
Lemma lem8054917 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term135 _143007 _143008 _143009 f s x t y) = (term223 _143007 _143008 _143009 f s x t y).
Proof. exact (MK_COMB (@lem8054916 _143007 _143008 _143009 s x f y) (@lem8054879 _143007 _143008 _143009 f s x t y)). Qed.
Lemma lem8054918 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8054919 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term195 _143007 _143008 _143009 f s x t y) = (term224 _143007 _143008 _143009 f s x t y).
Proof. exact (MK_COMB (@lem8054918) (@lem8054917 _143007 _143008 _143009 f s x t y)). Qed.
Lemma lem8054920 {_143007 _143008 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term197 _143007 _143008 _143009 t f s x y) = (term225 _143007 _143008 _143009 t f s x y).
Proof. exact (MK_COMB (@lem8054919 _143007 _143008 _143009 f s x t y) (@lem8054845 _143007 _143008 _143009 t f s x y)). Qed.
Lemma lem8054921 {_143007 _143008 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term197 _143007 _143008 _143009 t f s x y) : term225 _143007 _143008 _143009 t f s x y.
Proof. exact (EQ_MP (@lem8054920 _143007 _143008 _143009 t f s x y) (@lem8054772 _143007 _143008 _143009 t f s x y h1)). Qed.
Lemma lem8054926 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8054927 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x : type24 _143007 _143009) : (f x) = (@I (((cart _143007 _143009) -> Prop) -> Prop) f x).
Proof. exact (@lem8054926 (type24 _143007 _143009) Prop f x). Qed.
Lemma lem8054929 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x' : type24 _143007 _143009) : (f x') = (@I (((cart _143007 _143009) -> Prop) -> Prop) f x').
Proof. exact (@lem8054927 _143007 _143009 f x'). Qed.
Lemma lem8054931 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term223 _143007 _143008 _143009 f s x t y) : term223 _143007 _143008 _143009 f s x t y.
Proof. exact (h1). Qed.
Lemma lem8054932 {_143007 _143008 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term215 _143007 _143008 _143009 t f s x y) : term215 _143007 _143008 _143009 t f s x y.
Proof. exact (h1). Qed.
Lemma lem8054933 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term223 _143007 _143008 _143009 f s x t y) : term217 _143007 _143008 _143009 f s x t y.
Proof. exact (proj2 (@lem8054931 _143007 _143008 _143009 f s x t y h1)). Qed.
Lemma lem8054934 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term223 _143007 _143008 _143009 f s x t y) : term221 _143007 _143008 _143009 s x f y.
Proof. exact (proj1 (@lem8054931 _143007 _143008 _143009 f s x t y h1)). Qed.
Lemma lem8054935 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term223 _143007 _143008 _143009 f s x t y) : term216 _143007 _143008 _143009 s x t y.
Proof. exact (proj2 (@lem8054933 _143007 _143008 _143009 f s x t y h1)). Qed.
Lemma lem8054937 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term223 _143007 _143008 _143009 f s x t y) : term220 _143007 _143009 f y.
Proof. exact (proj2 (@lem8054934 _143007 _143008 _143009 f s x t y h1)). Qed.
Lemma lem8054941 {_143007 _143008 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term215 _143007 _143008 _143009 t f s x y) : term208 _143007 _143008 _143009 f s x y.
Proof. exact (proj2 (@lem8054932 _143007 _143008 _143009 t f s x y h1)). Qed.
Lemma lem8054942 {_143007 _143008 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term215 _143007 _143008 _143009 t f s x y) : term213 _143007 _143008 _143009 s x f t y.
Proof. exact (proj1 (@lem8054932 _143007 _143008 _143009 t f s x y h1)). Qed.
Lemma lem8054944 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term211 _143007 _143009 f t y) : term211 _143007 _143009 f t y.
Proof. exact (h1). Qed.
Lemma lem8054975 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (h1 : term209 _143007 _143008 s x) : term209 _143007 _143008 s x.
Proof. exact (h1). Qed.
Lemma lem8054995 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term218 _143007 _143009 f t y) = (term218 _143007 _143009 f t y).
Proof. exact (eq_refl (term218 _143007 _143009 f t y)). Qed.
Lemma lem8054996 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term219 _143007 _143009 f y) = (term219 _143007 _143009 f y).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8054995 _143007 _143009 f t y)). Qed.
Lemma lem8054997 {_143007 _143009 : Type'} : (@all ((cart _143007 _143009) -> Prop)) = (@all ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8054999 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term220 _143007 _143009 f y) = (term220 _143007 _143009 f y).
Proof. exact (MK_COMB (@lem8054997 _143007 _143009) (@lem8054996 _143007 _143009 f y)). Qed.
Lemma lem8055000 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term223 _143007 _143008 _143009 f s x t y) : term220 _143007 _143009 f y.
Proof. exact (EQ_MP (@lem8054999 _143007 _143009 f y) (@lem8054937 _143007 _143008 _143009 f s x t y h1)). Qed.
Lemma lem8055004 {_143007 _143009 : Type'} (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term209 _143007 _143009 t y) : term209 _143007 _143009 t y.
Proof. exact (h1). Qed.
Lemma lem8055026 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term206 _143007 _143008 _143009 f s x t y) = (term226 _143007 _143008 _143009 s x f t y).
Proof. exact (@lem19490 (@I ((cart _143007 _143008) -> Prop) s x) (term203 _143007 _143009 f t) (@I ((cart _143007 _143009) -> Prop) t y)). Qed.
Lemma lem8055027 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term207 _143007 _143008 _143009 f s x y) = (term227 _143007 _143008 _143009 s x f y).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8055026 _143007 _143008 _143009 s x f t y)). Qed.
Lemma lem8055028 {_143007 _143009 : Type'} : (@all ((cart _143007 _143009) -> Prop)) = (@all ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8055030 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term208 _143007 _143008 _143009 f s x y) = (term228 _143007 _143008 _143009 s x f y).
Proof. exact (MK_COMB (@lem8055028 _143007 _143009) (@lem8055027 _143007 _143008 _143009 s x f y)). Qed.
Lemma lem8055031 {_143007 _143008 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term215 _143007 _143008 _143009 t f s x y) : term228 _143007 _143008 _143009 s x f y.
Proof. exact (EQ_MP (@lem8055030 _143007 _143008 _143009 s x f y) (@lem8054941 _143007 _143008 _143009 t f s x y h1)). Qed.
Lemma lem8055035 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (h1 : term209 _143007 _143008 s x) : term209 _143007 _143008 s x.
Proof. exact (h1). Qed.
Lemma lem8055057 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term206 _143007 _143008 _143009 f s x t y) = (term226 _143007 _143008 _143009 s x f t y).
Proof. exact (@lem19490 (@I ((cart _143007 _143008) -> Prop) s x) (term203 _143007 _143009 f t) (@I ((cart _143007 _143009) -> Prop) t y)). Qed.
Lemma lem8055058 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term207 _143007 _143008 _143009 f s x y) = (term227 _143007 _143008 _143009 s x f y).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8055057 _143007 _143008 _143009 s x f t y)). Qed.
Lemma lem8055059 {_143007 _143009 : Type'} : (@all ((cart _143007 _143009) -> Prop)) = (@all ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8055061 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (y : cart _143007 _143009) : (term208 _143007 _143008 _143009 f s x y) = (term228 _143007 _143008 _143009 s x f y).
Proof. exact (MK_COMB (@lem8055059 _143007 _143009) (@lem8055058 _143007 _143008 _143009 s x f y)). Qed.
Lemma lem8055062 {_143007 _143008 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term215 _143007 _143008 _143009 t f s x y) : term228 _143007 _143008 _143009 s x f y.
Proof. exact (EQ_MP (@lem8055061 _143007 _143008 _143009 s x f y) (@lem8054941 _143007 _143008 _143009 t f s x y h1)). Qed.
Lemma lem8055074 {_143007 _143008 _143009 : Type'} (_106210 : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term223 _143007 _143008 _143009 f s x t y) : term229 _143007 _143009 f y _106210.
Proof. exact (@lem8055000 _143007 _143008 _143009 f s x t y h1 _106210). Qed.
Lemma lem8055075 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (_106210 : type24 _143007 _143009) (y : cart _143007 _143009) : (term229 _143007 _143009 f y _106210) = (term218 _143007 _143009 f _106210 y).
Proof. exact (eq_refl (term229 _143007 _143009 f y _106210)). Qed.
Lemma lem8055077 {_143007 _143008 _143009 : Type'} (_106211 : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term215 _143007 _143008 _143009 t f s x y) : term230 _143007 _143008 _143009 s x f y _106211.
Proof. exact (@lem8055031 _143007 _143008 _143009 t f s x y h1 _106211). Qed.
Lemma lem8055078 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (_106211 : type24 _143007 _143009) (y : cart _143007 _143009) : (term230 _143007 _143008 _143009 s x f y _106211) = (term226 _143007 _143008 _143009 s x f _106211 y).
Proof. exact (eq_refl (term230 _143007 _143008 _143009 s x f y _106211)). Qed.
Lemma lem8055079 {_143007 _143008 _143009 : Type'} (_106211 : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term215 _143007 _143008 _143009 t f s x y) : term226 _143007 _143008 _143009 s x f _106211 y.
Proof. exact (EQ_MP (@lem8055078 _143007 _143008 _143009 s x f _106211 y) (@lem8055077 _143007 _143008 _143009 _106211 t f s x y h1)). Qed.
Lemma lem8055080 {_143007 _143008 _143009 : Type'} (_106212 : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term215 _143007 _143008 _143009 t f s x y) : term230 _143007 _143008 _143009 s x f y _106212.
Proof. exact (@lem8055062 _143007 _143008 _143009 t f s x y h1 _106212). Qed.
Lemma lem8055081 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (_106212 : type24 _143007 _143009) (y : cart _143007 _143009) : (term230 _143007 _143008 _143009 s x f y _106212) = (term226 _143007 _143008 _143009 s x f _106212 y).
Proof. exact (eq_refl (term230 _143007 _143008 _143009 s x f y _106212)). Qed.
Lemma lem8055082 {_143007 _143008 _143009 : Type'} (_106212 : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term215 _143007 _143008 _143009 t f s x y) : term226 _143007 _143008 _143009 s x f _106212 y.
Proof. exact (EQ_MP (@lem8055081 _143007 _143008 _143009 s x f _106212 y) (@lem8055080 _143007 _143008 _143009 _106212 t f s x y h1)). Qed.
Lemma lem8055100 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (h1 : term209 _143007 _143008 s x) : term209 _143007 _143008 s x.
Proof. exact (h1). Qed.
Lemma lem8055112 {_143007 _143008 _143009 : Type'} (_106210 : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term223 _143007 _143008 _143009 f s x t y) : term218 _143007 _143009 f _106210 y.
Proof. exact (EQ_MP (@lem8055075 _143007 _143009 f _106210 y) (@lem8055074 _143007 _143008 _143009 _106210 f s x t y h1)). Qed.
Lemma lem8055114 {_143007 _143009 : Type'} (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term209 _143007 _143009 t y) : term209 _143007 _143009 t y.
Proof. exact (h1). Qed.
Lemma lem8055118 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (h1 : term209 _143007 _143008 s x) : term209 _143007 _143008 s x.
Proof. exact (h1). Qed.
Lemma lem8055124 {_143007 _143008 _143009 : Type'} (_106211 : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term215 _143007 _143008 _143009 t f s x y) : term231 _143007 _143008 _143009 f _106211 s x.
Proof. exact (proj1 (@lem8055079 _143007 _143008 _143009 _106211 t f s x y h1)). Qed.
Lemma lem8055136 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term211 _143007 _143009 f t y) : term209 _143007 _143009 t y.
Proof. exact (proj2 (@lem8054944 _143007 _143009 f t y h1)). Qed.
Lemma lem8055148 {_143007 _143008 _143009 : Type'} (_106212 : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term215 _143007 _143008 _143009 t f s x y) : term218 _143007 _143009 f _106212 y.
Proof. exact (proj2 (@lem8055082 _143007 _143008 _143009 _106212 t f s x y h1)). Qed.
Lemma lem8055150 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term223 _143007 _143008 _143009 f s x t y) : @I ((cart _143007 _143008) -> Prop) s x.
Proof. exact (proj1 (@lem8054934 _143007 _143008 _143009 f s x t y h1)). Qed.
Lemma lem8055151 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term223 _143007 _143008 _143009 f s x t y) : term232 _143007 _143008 s x.
Proof. exact (fun h0 : term209 _143007 _143008 s x => @lem8055150 _143007 _143008 _143009 f s x t y h1). Qed.
Lemma lem8055153 (p : Prop) : (term233 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8055154 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term232 _143007 _143008 s x) = (@I ((cart _143007 _143008) -> Prop) s x).
Proof. exact (@lem8055153 (@I ((cart _143007 _143008) -> Prop) s x)). Qed.
Lemma lem8055155 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term223 _143007 _143008 _143009 f s x t y) : @I ((cart _143007 _143008) -> Prop) s x.
Proof. exact (EQ_MP (@lem8055154 _143007 _143008 s x) (@lem8055151 _143007 _143008 _143009 f s x t y h1)). Qed.
Lemma lem8055158 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8055160 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term209 _143007 _143008 s x) = (term234 _143007 _143008 s x).
Proof. exact (@lem8055158 (@I ((cart _143007 _143008) -> Prop) s x)). Qed.
Lemma lem8055163 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (h1 : term209 _143007 _143008 s x) : term234 _143007 _143008 s x.
Proof. exact (EQ_MP (@lem8055160 _143007 _143008 s x) (@lem8055100 _143007 _143008 s x h1)). Qed.
Lemma lem8055166 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term209 _143007 _143008 s x) (h2 : term223 _143007 _143008 _143009 f s x t y) : False.
Proof. exact (@lem8055163 _143007 _143008 s x h1 (@lem8055155 _143007 _143008 _143009 f s x t y h2)). Qed.
Lemma lem8055167 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term209 _143007 _143008 s x) (h2 : term223 _143007 _143008 _143009 f s x t y) : term235.
Proof. exact (fun h0 : ~ False => @lem8055166 _143007 _143008 _143009 f s x t y h1 h2). Qed.
Lemma lem8055169 (p : Prop) : (term233 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8055170 : term235 = False.
Proof. exact (@lem8055169 False). Qed.
Lemma lem8055171 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term209 _143007 _143008 s x) (h2 : term223 _143007 _143008 _143009 f s x t y) : False.
Proof. exact (EQ_MP (@lem8055170) (@lem8055167 _143007 _143008 _143009 f s x t y h1 h2)). Qed.
Lemma lem8055173 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term223 _143007 _143008 _143009 f s x t y) : @I (((cart _143007 _143009) -> Prop) -> Prop) f t.
Proof. exact (proj1 (@lem8054933 _143007 _143008 _143009 f s x t y h1)). Qed.
Lemma lem8055174 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term223 _143007 _143008 _143009 f s x t y) : term236 _143007 _143009 f t.
Proof. exact (fun h0 : term203 _143007 _143009 f t => @lem8055173 _143007 _143008 _143009 f s x t y h1). Qed.
Lemma lem8055176 (p : Prop) : (term233 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8055177 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) : (term236 _143007 _143009 f t) = (@I (((cart _143007 _143009) -> Prop) -> Prop) f t).
Proof. exact (@lem8055176 (@I (((cart _143007 _143009) -> Prop) -> Prop) f t)). Qed.
Lemma lem8055178 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term223 _143007 _143008 _143009 f s x t y) : @I (((cart _143007 _143009) -> Prop) -> Prop) f t.
Proof. exact (EQ_MP (@lem8055177 _143007 _143009 f t) (@lem8055174 _143007 _143008 _143009 f s x t y h1)). Qed.
Lemma lem8055184 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8055185 {_143007 _143009 : Type'} (y : cart _143007 _143009) (f : type56 _143007 _143009) (_106210 : type24 _143007 _143009) : (term218 _143007 _143009 f _106210 y) = (term237 _143007 _143009 y f _106210).
Proof. exact (@lem8055184 (@I ((cart _143007 _143009) -> Prop) _106210 y) (term203 _143007 _143009 f _106210)). Qed.
Lemma lem8055191 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8055192 {_143007 _143009 : Type'} (y : cart _143007 _143009) (f : type56 _143007 _143009) (_106210 : type24 _143007 _143009) : (term238 _143007 _143009 f _106210 y) = (term239 _143007 _143009 y f _106210).
Proof. exact (MK_COMB (@lem8055191) (@lem8055185 _143007 _143009 y f _106210)). Qed.
Lemma lem8055198 {_143007 _143009 : Type'} (y : cart _143007 _143009) (f : type56 _143007 _143009) (_106210 : type24 _143007 _143009) : (term237 _143007 _143009 y f _106210) = (term237 _143007 _143009 y f _106210).
Proof. exact (eq_refl (term237 _143007 _143009 y f _106210)). Qed.
Lemma lem8055199 {_143007 _143009 : Type'} (y : cart _143007 _143009) (f : type56 _143007 _143009) (_106210 : type24 _143007 _143009) : ((term218 _143007 _143009 f _106210 y) = (term237 _143007 _143009 y f _106210)) = ((term237 _143007 _143009 y f _106210) = (term237 _143007 _143009 y f _106210)).
Proof. exact (MK_COMB (@lem8055192 _143007 _143009 y f _106210) (@lem8055198 _143007 _143009 y f _106210)). Qed.
Lemma lem8055201 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8055202 (x : Prop) : (x = x) = True.
Proof. exact (@lem8055201 Prop x). Qed.
Lemma lem8055203 {_143007 _143009 : Type'} (y : cart _143007 _143009) (f : type56 _143007 _143009) (_106210 : type24 _143007 _143009) : ((term237 _143007 _143009 y f _106210) = (term237 _143007 _143009 y f _106210)) = True.
Proof. exact (@lem8055202 (term237 _143007 _143009 y f _106210)). Qed.
Lemma lem8055204 {_143007 _143009 : Type'} (y : cart _143007 _143009) (f : type56 _143007 _143009) (_106210 : type24 _143007 _143009) : ((term218 _143007 _143009 f _106210 y) = (term237 _143007 _143009 y f _106210)) = True.
Proof. exact (TRANS (@lem8055199 _143007 _143009 y f _106210) (@lem8055203 _143007 _143009 y f _106210)). Qed.
Lemma lem8055205 {_143007 _143009 : Type'} (y : cart _143007 _143009) (f : type56 _143007 _143009) (_106210 : type24 _143007 _143009) : True = ((term218 _143007 _143009 f _106210 y) = (term237 _143007 _143009 y f _106210)).
Proof. exact (SYM (@lem8055204 _143007 _143009 y f _106210)). Qed.
Lemma lem8055206 {_143007 _143009 : Type'} (y : cart _143007 _143009) (f : type56 _143007 _143009) (_106210 : type24 _143007 _143009) : (term218 _143007 _143009 f _106210 y) = (term237 _143007 _143009 y f _106210).
Proof. exact (EQ_MP (@lem8055205 _143007 _143009 y f _106210) (@lem0)). Qed.
Lemma lem8055207 {_143007 _143008 _143009 : Type'} (_106210 : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term223 _143007 _143008 _143009 f s x t y) : term237 _143007 _143009 y f _106210.
Proof. exact (EQ_MP (@lem8055206 _143007 _143009 y f _106210) (@lem8055112 _143007 _143008 _143009 _106210 f s x t y h1)). Qed.
Lemma lem8055209 (b : Prop) (a : Prop) : (a \/ b) = (term240 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8055210 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (_106210 : type24 _143007 _143009) (y : cart _143007 _143009) : (term237 _143007 _143009 y f _106210) = (term241 _143007 _143009 f _106210 y).
Proof. exact (@lem8055209 (term203 _143007 _143009 f _106210) (@I ((cart _143007 _143009) -> Prop) _106210 y)). Qed.
Lemma lem8055212 (a : Prop) : (term58 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8055213 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (_106210 : type24 _143007 _143009) : (term242 _143007 _143009 f _106210) = (@I (((cart _143007 _143009) -> Prop) -> Prop) f _106210).
Proof. exact (@lem8055212 (@I (((cart _143007 _143009) -> Prop) -> Prop) f _106210)). Qed.
Lemma lem8055214 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8055215 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (_106210 : type24 _143007 _143009) : (term243 _143007 _143009 f _106210) = (term244 _143007 _143009 f _106210).
Proof. exact (MK_COMB (@lem8055214) (@lem8055213 _143007 _143009 f _106210)). Qed.
Lemma lem8055216 {_143007 _143009 : Type'} (_106210 : type24 _143007 _143009) (y : cart _143007 _143009) : (@I ((cart _143007 _143009) -> Prop) _106210 y) = (@I ((cart _143007 _143009) -> Prop) _106210 y).
Proof. exact (eq_refl (@I ((cart _143007 _143009) -> Prop) _106210 y)). Qed.
Lemma lem8055217 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (_106210 : type24 _143007 _143009) (y : cart _143007 _143009) : (term241 _143007 _143009 f _106210 y) = (term245 _143007 _143009 f _106210 y).
Proof. exact (MK_COMB (@lem8055215 _143007 _143009 f _106210) (@lem8055216 _143007 _143009 _106210 y)). Qed.
Lemma lem8055218 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (_106210 : type24 _143007 _143009) (y : cart _143007 _143009) : (term237 _143007 _143009 y f _106210) = (term245 _143007 _143009 f _106210 y).
Proof. exact (TRANS (@lem8055210 _143007 _143009 f _106210 y) (@lem8055217 _143007 _143009 f _106210 y)). Qed.
Lemma lem8055221 {_143007 _143008 _143009 : Type'} (_106210 : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term223 _143007 _143008 _143009 f s x t y) : term245 _143007 _143009 f _106210 y.
Proof. exact (EQ_MP (@lem8055218 _143007 _143009 f _106210 y) (@lem8055207 _143007 _143008 _143009 _106210 f s x t y h1)). Qed.
Lemma lem8055222 {_143007 _143008 _143009 : Type'} (_106210 : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term223 _143007 _143008 _143009 f s x t y) : term245 _143007 _143009 f _106210 y.
Proof. exact (@lem8055221 _143007 _143008 _143009 _106210 f s x t y h1). Qed.
Lemma lem8055223 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term223 _143007 _143008 _143009 f s x t y) : term245 _143007 _143009 f t y.
Proof. exact (@lem8055222 _143007 _143008 _143009 t f s x t y h1). Qed.
Lemma lem8055226 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term223 _143007 _143008 _143009 f s x t y) : @I ((cart _143007 _143009) -> Prop) t y.
Proof. exact (@lem8055223 _143007 _143008 _143009 f s x t y h1 (@lem8055178 _143007 _143008 _143009 f s x t y h1)). Qed.
Lemma lem8055227 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term223 _143007 _143008 _143009 f s x t y) : term232 _143007 _143009 t y.
Proof. exact (fun h0 : term209 _143007 _143009 t y => @lem8055226 _143007 _143008 _143009 f s x t y h1). Qed.
Lemma lem8055229 (p : Prop) : (term233 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8055230 {_143007 _143009 : Type'} (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term232 _143007 _143009 t y) = (@I ((cart _143007 _143009) -> Prop) t y).
Proof. exact (@lem8055229 (@I ((cart _143007 _143009) -> Prop) t y)). Qed.
Lemma lem8055231 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term223 _143007 _143008 _143009 f s x t y) : @I ((cart _143007 _143009) -> Prop) t y.
Proof. exact (EQ_MP (@lem8055230 _143007 _143009 t y) (@lem8055227 _143007 _143008 _143009 f s x t y h1)). Qed.
Lemma lem8055234 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8055236 {_143007 _143009 : Type'} (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term209 _143007 _143009 t y) = (term234 _143007 _143009 t y).
Proof. exact (@lem8055234 (@I ((cart _143007 _143009) -> Prop) t y)). Qed.
Lemma lem8055239 {_143007 _143009 : Type'} (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term209 _143007 _143009 t y) : term234 _143007 _143009 t y.
Proof. exact (EQ_MP (@lem8055236 _143007 _143009 t y) (@lem8055114 _143007 _143009 t y h1)). Qed.
Lemma lem8055242 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term209 _143007 _143009 t y) (h2 : term223 _143007 _143008 _143009 f s x t y) : False.
Proof. exact (@lem8055239 _143007 _143009 t y h1 (@lem8055231 _143007 _143008 _143009 f s x t y h2)). Qed.
Lemma lem8055243 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term209 _143007 _143009 t y) (h2 : term223 _143007 _143008 _143009 f s x t y) : term235.
Proof. exact (fun h0 : ~ False => @lem8055242 _143007 _143008 _143009 f s x t y h1 h2). Qed.
Lemma lem8055245 (p : Prop) : (term233 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8055246 : term235 = False.
Proof. exact (@lem8055245 False). Qed.
Lemma lem8055247 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term209 _143007 _143009 t y) (h2 : term223 _143007 _143008 _143009 f s x t y) : False.
Proof. exact (EQ_MP (@lem8055246) (@lem8055243 _143007 _143008 _143009 f s x t y h1 h2)). Qed.
Lemma lem8055249 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x' : type24 _143007 _143009) (h1 : f x') : @I (((cart _143007 _143009) -> Prop) -> Prop) f x'.
Proof. exact (EQ_MP (@lem8054929 _143007 _143009 f x') (@lem8054773 _143007 _143009 f x' h1)). Qed.
Lemma lem8055250 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x' : type24 _143007 _143009) (h1 : f x') : term236 _143007 _143009 f x'.
Proof. exact (fun h0 : term203 _143007 _143009 f x' => @lem8055249 _143007 _143009 f x' h1). Qed.
Lemma lem8055252 (p : Prop) : (term233 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8055253 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x' : type24 _143007 _143009) : (term236 _143007 _143009 f x') = (@I (((cart _143007 _143009) -> Prop) -> Prop) f x').
Proof. exact (@lem8055252 (@I (((cart _143007 _143009) -> Prop) -> Prop) f x')). Qed.
Lemma lem8055254 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (x' : type24 _143007 _143009) (h1 : f x') : @I (((cart _143007 _143009) -> Prop) -> Prop) f x'.
Proof. exact (EQ_MP (@lem8055253 _143007 _143009 f x') (@lem8055250 _143007 _143009 f x' h1)). Qed.
Lemma lem8055260 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8055261 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (_106211 : type24 _143007 _143009) : (term231 _143007 _143008 _143009 f _106211 s x) = (term246 _143007 _143008 _143009 s x f _106211).
Proof. exact (@lem8055260 (@I ((cart _143007 _143008) -> Prop) s x) (term203 _143007 _143009 f _106211)). Qed.
Lemma lem8055267 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8055268 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (_106211 : type24 _143007 _143009) : (term247 _143007 _143008 _143009 f _106211 s x) = (term248 _143007 _143008 _143009 s x f _106211).
Proof. exact (MK_COMB (@lem8055267) (@lem8055261 _143007 _143008 _143009 s x f _106211)). Qed.
Lemma lem8055274 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (_106211 : type24 _143007 _143009) : (term246 _143007 _143008 _143009 s x f _106211) = (term246 _143007 _143008 _143009 s x f _106211).
Proof. exact (eq_refl (term246 _143007 _143008 _143009 s x f _106211)). Qed.
Lemma lem8055275 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (_106211 : type24 _143007 _143009) : ((term231 _143007 _143008 _143009 f _106211 s x) = (term246 _143007 _143008 _143009 s x f _106211)) = ((term246 _143007 _143008 _143009 s x f _106211) = (term246 _143007 _143008 _143009 s x f _106211)).
Proof. exact (MK_COMB (@lem8055268 _143007 _143008 _143009 s x f _106211) (@lem8055274 _143007 _143008 _143009 s x f _106211)). Qed.
Lemma lem8055277 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8055278 (x : Prop) : (x = x) = True.
Proof. exact (@lem8055277 Prop x). Qed.
Lemma lem8055279 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (_106211 : type24 _143007 _143009) : ((term246 _143007 _143008 _143009 s x f _106211) = (term246 _143007 _143008 _143009 s x f _106211)) = True.
Proof. exact (@lem8055278 (term246 _143007 _143008 _143009 s x f _106211)). Qed.
Lemma lem8055280 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (_106211 : type24 _143007 _143009) : ((term231 _143007 _143008 _143009 f _106211 s x) = (term246 _143007 _143008 _143009 s x f _106211)) = True.
Proof. exact (TRANS (@lem8055275 _143007 _143008 _143009 s x f _106211) (@lem8055279 _143007 _143008 _143009 s x f _106211)). Qed.
Lemma lem8055281 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (_106211 : type24 _143007 _143009) : True = ((term231 _143007 _143008 _143009 f _106211 s x) = (term246 _143007 _143008 _143009 s x f _106211)).
Proof. exact (SYM (@lem8055280 _143007 _143008 _143009 s x f _106211)). Qed.
Lemma lem8055282 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (_106211 : type24 _143007 _143009) : (term231 _143007 _143008 _143009 f _106211 s x) = (term246 _143007 _143008 _143009 s x f _106211).
Proof. exact (EQ_MP (@lem8055281 _143007 _143008 _143009 s x f _106211) (@lem0)). Qed.
Lemma lem8055283 {_143007 _143008 _143009 : Type'} (_106211 : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term215 _143007 _143008 _143009 t f s x y) : term246 _143007 _143008 _143009 s x f _106211.
Proof. exact (EQ_MP (@lem8055282 _143007 _143008 _143009 s x f _106211) (@lem8055124 _143007 _143008 _143009 _106211 t f s x y h1)). Qed.
Lemma lem8055285 (b : Prop) (a : Prop) : (a \/ b) = (term240 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8055286 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (_106211 : type24 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term246 _143007 _143008 _143009 s x f _106211) = (term249 _143007 _143008 _143009 f _106211 s x).
Proof. exact (@lem8055285 (term203 _143007 _143009 f _106211) (@I ((cart _143007 _143008) -> Prop) s x)). Qed.
Lemma lem8055288 (a : Prop) : (term58 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8055289 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (_106211 : type24 _143007 _143009) : (term242 _143007 _143009 f _106211) = (@I (((cart _143007 _143009) -> Prop) -> Prop) f _106211).
Proof. exact (@lem8055288 (@I (((cart _143007 _143009) -> Prop) -> Prop) f _106211)). Qed.
Lemma lem8055290 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8055291 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (_106211 : type24 _143007 _143009) : (term243 _143007 _143009 f _106211) = (term244 _143007 _143009 f _106211).
Proof. exact (MK_COMB (@lem8055290) (@lem8055289 _143007 _143009 f _106211)). Qed.
Lemma lem8055292 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (@I ((cart _143007 _143008) -> Prop) s x) = (@I ((cart _143007 _143008) -> Prop) s x).
Proof. exact (eq_refl (@I ((cart _143007 _143008) -> Prop) s x)). Qed.
Lemma lem8055293 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (_106211 : type24 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term249 _143007 _143008 _143009 f _106211 s x) = (term250 _143007 _143008 _143009 f _106211 s x).
Proof. exact (MK_COMB (@lem8055291 _143007 _143009 f _106211) (@lem8055292 _143007 _143008 s x)). Qed.
Lemma lem8055294 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (_106211 : type24 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term246 _143007 _143008 _143009 s x f _106211) = (term250 _143007 _143008 _143009 f _106211 s x).
Proof. exact (TRANS (@lem8055286 _143007 _143008 _143009 f _106211 s x) (@lem8055293 _143007 _143008 _143009 f _106211 s x)). Qed.
Lemma lem8055297 {_143007 _143008 _143009 : Type'} (_106211 : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term215 _143007 _143008 _143009 t f s x y) : term250 _143007 _143008 _143009 f _106211 s x.
Proof. exact (EQ_MP (@lem8055294 _143007 _143008 _143009 f _106211 s x) (@lem8055283 _143007 _143008 _143009 _106211 t f s x y h1)). Qed.
Lemma lem8055298 {_143007 _143008 _143009 : Type'} (_106211 : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term215 _143007 _143008 _143009 t f s x y) : term250 _143007 _143008 _143009 f _106211 s x.
Proof. exact (@lem8055297 _143007 _143008 _143009 _106211 t f s x y h1). Qed.
Lemma lem8055299 {_143007 _143008 _143009 : Type'} (x' : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term215 _143007 _143008 _143009 t f s x y) : term250 _143007 _143008 _143009 f x' s x.
Proof. exact (@lem8055298 _143007 _143008 _143009 x' t f s x y h1). Qed.
Lemma lem8055302 {_143007 _143008 _143009 : Type'} (x' : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : f x') (h2 : term215 _143007 _143008 _143009 t f s x y) : @I ((cart _143007 _143008) -> Prop) s x.
Proof. exact (@lem8055299 _143007 _143008 _143009 x' t f s x y h2 (@lem8055254 _143007 _143009 f x' h1)). Qed.
Lemma lem8055303 {_143007 _143008 _143009 : Type'} (x' : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : f x') (h2 : term215 _143007 _143008 _143009 t f s x y) : term232 _143007 _143008 s x.
Proof. exact (fun h0 : term209 _143007 _143008 s x => @lem8055302 _143007 _143008 _143009 x' t f s x y h1 h2). Qed.
Lemma lem8055305 (p : Prop) : (term233 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8055306 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term232 _143007 _143008 s x) = (@I ((cart _143007 _143008) -> Prop) s x).
Proof. exact (@lem8055305 (@I ((cart _143007 _143008) -> Prop) s x)). Qed.
Lemma lem8055307 {_143007 _143008 _143009 : Type'} (x' : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : f x') (h2 : term215 _143007 _143008 _143009 t f s x y) : @I ((cart _143007 _143008) -> Prop) s x.
Proof. exact (EQ_MP (@lem8055306 _143007 _143008 s x) (@lem8055303 _143007 _143008 _143009 x' t f s x y h1 h2)). Qed.
Lemma lem8055310 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8055312 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) : (term209 _143007 _143008 s x) = (term234 _143007 _143008 s x).
Proof. exact (@lem8055310 (@I ((cart _143007 _143008) -> Prop) s x)). Qed.
Lemma lem8055315 {_143007 _143008 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (h1 : term209 _143007 _143008 s x) : term234 _143007 _143008 s x.
Proof. exact (EQ_MP (@lem8055312 _143007 _143008 s x) (@lem8055118 _143007 _143008 s x h1)). Qed.
Lemma lem8055318 {_143007 _143008 _143009 : Type'} (x' : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term209 _143007 _143008 s x) (h2 : f x') (h3 : term215 _143007 _143008 _143009 t f s x y) : False.
Proof. exact (@lem8055315 _143007 _143008 s x h1 (@lem8055307 _143007 _143008 _143009 x' t f s x y h2 h3)). Qed.
Lemma lem8055319 {_143007 _143008 _143009 : Type'} (x' : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term209 _143007 _143008 s x) (h2 : f x') (h3 : term215 _143007 _143008 _143009 t f s x y) : term235.
Proof. exact (fun h0 : ~ False => @lem8055318 _143007 _143008 _143009 x' t f s x y h1 h2 h3). Qed.
Lemma lem8055321 (p : Prop) : (term233 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8055322 : term235 = False.
Proof. exact (@lem8055321 False). Qed.
Lemma lem8055323 {_143007 _143008 _143009 : Type'} (x' : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term209 _143007 _143008 s x) (h2 : f x') (h3 : term215 _143007 _143008 _143009 t f s x y) : False.
Proof. exact (EQ_MP (@lem8055322) (@lem8055319 _143007 _143008 _143009 x' t f s x y h1 h2 h3)). Qed.
Lemma lem8055325 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term211 _143007 _143009 f t y) : @I (((cart _143007 _143009) -> Prop) -> Prop) f t.
Proof. exact (proj1 (@lem8054944 _143007 _143009 f t y h1)). Qed.
Lemma lem8055326 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term211 _143007 _143009 f t y) : term236 _143007 _143009 f t.
Proof. exact (fun h0 : term203 _143007 _143009 f t => @lem8055325 _143007 _143009 f t y h1). Qed.
Lemma lem8055328 (p : Prop) : (term233 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8055329 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) : (term236 _143007 _143009 f t) = (@I (((cart _143007 _143009) -> Prop) -> Prop) f t).
Proof. exact (@lem8055328 (@I (((cart _143007 _143009) -> Prop) -> Prop) f t)). Qed.
Lemma lem8055330 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term211 _143007 _143009 f t y) : @I (((cart _143007 _143009) -> Prop) -> Prop) f t.
Proof. exact (EQ_MP (@lem8055329 _143007 _143009 f t) (@lem8055326 _143007 _143009 f t y h1)). Qed.
Lemma lem8055336 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8055337 {_143007 _143009 : Type'} (y : cart _143007 _143009) (f : type56 _143007 _143009) (_106212 : type24 _143007 _143009) : (term218 _143007 _143009 f _106212 y) = (term237 _143007 _143009 y f _106212).
Proof. exact (@lem8055336 (@I ((cart _143007 _143009) -> Prop) _106212 y) (term203 _143007 _143009 f _106212)). Qed.
Lemma lem8055343 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8055344 {_143007 _143009 : Type'} (y : cart _143007 _143009) (f : type56 _143007 _143009) (_106212 : type24 _143007 _143009) : (term238 _143007 _143009 f _106212 y) = (term239 _143007 _143009 y f _106212).
Proof. exact (MK_COMB (@lem8055343) (@lem8055337 _143007 _143009 y f _106212)). Qed.
Lemma lem8055350 {_143007 _143009 : Type'} (y : cart _143007 _143009) (f : type56 _143007 _143009) (_106212 : type24 _143007 _143009) : (term237 _143007 _143009 y f _106212) = (term237 _143007 _143009 y f _106212).
Proof. exact (eq_refl (term237 _143007 _143009 y f _106212)). Qed.
Lemma lem8055351 {_143007 _143009 : Type'} (y : cart _143007 _143009) (f : type56 _143007 _143009) (_106212 : type24 _143007 _143009) : ((term218 _143007 _143009 f _106212 y) = (term237 _143007 _143009 y f _106212)) = ((term237 _143007 _143009 y f _106212) = (term237 _143007 _143009 y f _106212)).
Proof. exact (MK_COMB (@lem8055344 _143007 _143009 y f _106212) (@lem8055350 _143007 _143009 y f _106212)). Qed.
Lemma lem8055353 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8055354 (x : Prop) : (x = x) = True.
Proof. exact (@lem8055353 Prop x). Qed.
Lemma lem8055355 {_143007 _143009 : Type'} (y : cart _143007 _143009) (f : type56 _143007 _143009) (_106212 : type24 _143007 _143009) : ((term237 _143007 _143009 y f _106212) = (term237 _143007 _143009 y f _106212)) = True.
Proof. exact (@lem8055354 (term237 _143007 _143009 y f _106212)). Qed.
Lemma lem8055356 {_143007 _143009 : Type'} (y : cart _143007 _143009) (f : type56 _143007 _143009) (_106212 : type24 _143007 _143009) : ((term218 _143007 _143009 f _106212 y) = (term237 _143007 _143009 y f _106212)) = True.
Proof. exact (TRANS (@lem8055351 _143007 _143009 y f _106212) (@lem8055355 _143007 _143009 y f _106212)). Qed.
Lemma lem8055357 {_143007 _143009 : Type'} (y : cart _143007 _143009) (f : type56 _143007 _143009) (_106212 : type24 _143007 _143009) : True = ((term218 _143007 _143009 f _106212 y) = (term237 _143007 _143009 y f _106212)).
Proof. exact (SYM (@lem8055356 _143007 _143009 y f _106212)). Qed.
Lemma lem8055358 {_143007 _143009 : Type'} (y : cart _143007 _143009) (f : type56 _143007 _143009) (_106212 : type24 _143007 _143009) : (term218 _143007 _143009 f _106212 y) = (term237 _143007 _143009 y f _106212).
Proof. exact (EQ_MP (@lem8055357 _143007 _143009 y f _106212) (@lem0)). Qed.
Lemma lem8055359 {_143007 _143008 _143009 : Type'} (_106212 : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term215 _143007 _143008 _143009 t f s x y) : term237 _143007 _143009 y f _106212.
Proof. exact (EQ_MP (@lem8055358 _143007 _143009 y f _106212) (@lem8055148 _143007 _143008 _143009 _106212 t f s x y h1)). Qed.
Lemma lem8055361 (b : Prop) (a : Prop) : (a \/ b) = (term240 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8055362 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (_106212 : type24 _143007 _143009) (y : cart _143007 _143009) : (term237 _143007 _143009 y f _106212) = (term241 _143007 _143009 f _106212 y).
Proof. exact (@lem8055361 (term203 _143007 _143009 f _106212) (@I ((cart _143007 _143009) -> Prop) _106212 y)). Qed.
Lemma lem8055364 (a : Prop) : (term58 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8055365 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (_106212 : type24 _143007 _143009) : (term242 _143007 _143009 f _106212) = (@I (((cart _143007 _143009) -> Prop) -> Prop) f _106212).
Proof. exact (@lem8055364 (@I (((cart _143007 _143009) -> Prop) -> Prop) f _106212)). Qed.
Lemma lem8055366 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8055367 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (_106212 : type24 _143007 _143009) : (term243 _143007 _143009 f _106212) = (term244 _143007 _143009 f _106212).
Proof. exact (MK_COMB (@lem8055366) (@lem8055365 _143007 _143009 f _106212)). Qed.
Lemma lem8055368 {_143007 _143009 : Type'} (_106212 : type24 _143007 _143009) (y : cart _143007 _143009) : (@I ((cart _143007 _143009) -> Prop) _106212 y) = (@I ((cart _143007 _143009) -> Prop) _106212 y).
Proof. exact (eq_refl (@I ((cart _143007 _143009) -> Prop) _106212 y)). Qed.
Lemma lem8055369 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (_106212 : type24 _143007 _143009) (y : cart _143007 _143009) : (term241 _143007 _143009 f _106212 y) = (term245 _143007 _143009 f _106212 y).
Proof. exact (MK_COMB (@lem8055367 _143007 _143009 f _106212) (@lem8055368 _143007 _143009 _106212 y)). Qed.
Lemma lem8055370 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (_106212 : type24 _143007 _143009) (y : cart _143007 _143009) : (term237 _143007 _143009 y f _106212) = (term245 _143007 _143009 f _106212 y).
Proof. exact (TRANS (@lem8055362 _143007 _143009 f _106212 y) (@lem8055369 _143007 _143009 f _106212 y)). Qed.
Lemma lem8055373 {_143007 _143008 _143009 : Type'} (_106212 : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term215 _143007 _143008 _143009 t f s x y) : term245 _143007 _143009 f _106212 y.
Proof. exact (EQ_MP (@lem8055370 _143007 _143009 f _106212 y) (@lem8055359 _143007 _143008 _143009 _106212 t f s x y h1)). Qed.
Lemma lem8055374 {_143007 _143008 _143009 : Type'} (_106212 : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term215 _143007 _143008 _143009 t f s x y) : term245 _143007 _143009 f _106212 y.
Proof. exact (@lem8055373 _143007 _143008 _143009 _106212 t f s x y h1). Qed.
Lemma lem8055375 {_143007 _143008 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term215 _143007 _143008 _143009 t f s x y) : term245 _143007 _143009 f t y.
Proof. exact (@lem8055374 _143007 _143008 _143009 t t f s x y h1). Qed.
Lemma lem8055378 {_143007 _143008 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term211 _143007 _143009 f t y) (h2 : term215 _143007 _143008 _143009 t f s x y) : @I ((cart _143007 _143009) -> Prop) t y.
Proof. exact (@lem8055375 _143007 _143008 _143009 t f s x y h2 (@lem8055330 _143007 _143009 f t y h1)). Qed.
Lemma lem8055379 {_143007 _143008 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term211 _143007 _143009 f t y) (h2 : term215 _143007 _143008 _143009 t f s x y) : term232 _143007 _143009 t y.
Proof. exact (fun h0 : term209 _143007 _143009 t y => @lem8055378 _143007 _143008 _143009 t f s x y h1 h2). Qed.
Lemma lem8055381 (p : Prop) : (term233 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8055382 {_143007 _143009 : Type'} (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term232 _143007 _143009 t y) = (@I ((cart _143007 _143009) -> Prop) t y).
Proof. exact (@lem8055381 (@I ((cart _143007 _143009) -> Prop) t y)). Qed.
Lemma lem8055383 {_143007 _143008 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term211 _143007 _143009 f t y) (h2 : term215 _143007 _143008 _143009 t f s x y) : @I ((cart _143007 _143009) -> Prop) t y.
Proof. exact (EQ_MP (@lem8055382 _143007 _143009 t y) (@lem8055379 _143007 _143008 _143009 t f s x y h1 h2)). Qed.
Lemma lem8055386 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8055388 {_143007 _143009 : Type'} (t : type24 _143007 _143009) (y : cart _143007 _143009) : (term209 _143007 _143009 t y) = (term234 _143007 _143009 t y).
Proof. exact (@lem8055386 (@I ((cart _143007 _143009) -> Prop) t y)). Qed.
Lemma lem8055391 {_143007 _143009 : Type'} (f : type56 _143007 _143009) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term211 _143007 _143009 f t y) : term234 _143007 _143009 t y.
Proof. exact (EQ_MP (@lem8055388 _143007 _143009 t y) (@lem8055136 _143007 _143009 f t y h1)). Qed.
Lemma lem8055394 {_143007 _143008 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term211 _143007 _143009 f t y) (h2 : term215 _143007 _143008 _143009 t f s x y) : False.
Proof. exact (@lem8055391 _143007 _143009 f t y h1 (@lem8055383 _143007 _143008 _143009 t f s x y h1 h2)). Qed.
Lemma lem8055395 {_143007 _143008 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term211 _143007 _143009 f t y) (h2 : term215 _143007 _143008 _143009 t f s x y) : term235.
Proof. exact (fun h0 : ~ False => @lem8055394 _143007 _143008 _143009 t f s x y h1 h2). Qed.
Lemma lem8055397 (p : Prop) : (term233 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8055398 : term235 = False.
Proof. exact (@lem8055397 False). Qed.
Lemma lem8055399 {_143007 _143008 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term211 _143007 _143009 f t y) (h2 : term215 _143007 _143008 _143009 t f s x y) : False.
Proof. exact (EQ_MP (@lem8055398) (@lem8055395 _143007 _143008 _143009 t f s x y h1 h2)). Qed.
Lemma lem8055400 {_143007 _143008 _143009 : Type'} (x' : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term209 _143007 _143008 s x) (h2 : f x') (h3 : term215 _143007 _143008 _143009 t f s x y) : (term209 _143007 _143008 s x) = False.
Proof. exact (prop_ext (fun h4 : term209 _143007 _143008 s x => @lem8055323 _143007 _143008 _143009 x' t f s x y h1 h2 h3) (fun h4 : False => @lem8055118 _143007 _143008 s x h1)). Qed.
Lemma lem8055401 {_143007 _143008 _143009 : Type'} (x' : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term209 _143007 _143008 s x) (h2 : f x') (h3 : term215 _143007 _143008 _143009 t f s x y) : False.
Proof. exact (EQ_MP (@lem8055400 _143007 _143008 _143009 x' t f s x y h1 h2 h3) (@lem8055118 _143007 _143008 s x h1)). Qed.
Lemma lem8055402 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term209 _143007 _143009 t y) (h2 : term223 _143007 _143008 _143009 f s x t y) : (term209 _143007 _143009 t y) = False.
Proof. exact (prop_ext (fun h3 : term209 _143007 _143009 t y => @lem8055247 _143007 _143008 _143009 f s x t y h1 h2) (fun h3 : False => @lem8055114 _143007 _143009 t y h1)). Qed.
Lemma lem8055403 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term209 _143007 _143009 t y) (h2 : term223 _143007 _143008 _143009 f s x t y) : False.
Proof. exact (EQ_MP (@lem8055402 _143007 _143008 _143009 f s x t y h1 h2) (@lem8055114 _143007 _143009 t y h1)). Qed.
Lemma lem8055404 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term209 _143007 _143008 s x) (h2 : term223 _143007 _143008 _143009 f s x t y) : (term209 _143007 _143008 s x) = False.
Proof. exact (prop_ext (fun h3 : term209 _143007 _143008 s x => @lem8055171 _143007 _143008 _143009 f s x t y h1 h2) (fun h3 : False => @lem8055100 _143007 _143008 s x h1)). Qed.
Lemma lem8055405 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term209 _143007 _143008 s x) (h2 : term223 _143007 _143008 _143009 f s x t y) : False.
Proof. exact (EQ_MP (@lem8055404 _143007 _143008 _143009 f s x t y h1 h2) (@lem8055100 _143007 _143008 s x h1)). Qed.
Lemma lem8055406 {_143007 _143008 _143009 : Type'} (x' : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term209 _143007 _143008 s x) (h2 : f x') (h3 : term215 _143007 _143008 _143009 t f s x y) : (term209 _143007 _143008 s x) = False.
Proof. exact (prop_ext (fun h4 : term209 _143007 _143008 s x => @lem8055401 _143007 _143008 _143009 x' t f s x y h1 h2 h3) (fun h4 : False => @lem8055035 _143007 _143008 s x h1)). Qed.
Lemma lem8055407 {_143007 _143008 _143009 : Type'} (x' : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term209 _143007 _143008 s x) (h2 : f x') (h3 : term215 _143007 _143008 _143009 t f s x y) : False.
Proof. exact (EQ_MP (@lem8055406 _143007 _143008 _143009 x' t f s x y h1 h2 h3) (@lem8055035 _143007 _143008 s x h1)). Qed.
Lemma lem8055408 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term209 _143007 _143009 t y) (h2 : term223 _143007 _143008 _143009 f s x t y) : (term209 _143007 _143009 t y) = False.
Proof. exact (prop_ext (fun h3 : term209 _143007 _143009 t y => @lem8055403 _143007 _143008 _143009 f s x t y h1 h2) (fun h3 : False => @lem8055004 _143007 _143009 t y h1)). Qed.
Lemma lem8055409 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term209 _143007 _143009 t y) (h2 : term223 _143007 _143008 _143009 f s x t y) : False.
Proof. exact (EQ_MP (@lem8055408 _143007 _143008 _143009 f s x t y h1 h2) (@lem8055004 _143007 _143009 t y h1)). Qed.
Lemma lem8055410 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term209 _143007 _143008 s x) (h2 : term223 _143007 _143008 _143009 f s x t y) : (term209 _143007 _143008 s x) = False.
Proof. exact (prop_ext (fun h3 : term209 _143007 _143008 s x => @lem8055405 _143007 _143008 _143009 f s x t y h1 h2) (fun h3 : False => @lem8054975 _143007 _143008 s x h1)). Qed.
Lemma lem8055411 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term209 _143007 _143008 s x) (h2 : term223 _143007 _143008 _143009 f s x t y) : False.
Proof. exact (EQ_MP (@lem8055410 _143007 _143008 _143009 f s x t y h1 h2) (@lem8054975 _143007 _143008 s x h1)). Qed.
Lemma lem8055412 {_143007 _143008 _143009 : Type'} (x' : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term209 _143007 _143008 s x) (h2 : f x') (h3 : term215 _143007 _143008 _143009 t f s x y) : (term209 _143007 _143008 s x) = False.
Proof. exact (prop_ext (fun h4 : term209 _143007 _143008 s x => @lem8055407 _143007 _143008 _143009 x' t f s x y h1 h2 h3) (fun h4 : False => @lem8055035 _143007 _143008 s x h1)). Qed.
Lemma lem8055413 {_143007 _143008 _143009 : Type'} (x' : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term209 _143007 _143008 s x) (h2 : f x') (h3 : term215 _143007 _143008 _143009 t f s x y) : False.
Proof. exact (EQ_MP (@lem8055412 _143007 _143008 _143009 x' t f s x y h1 h2 h3) (@lem8055035 _143007 _143008 s x h1)). Qed.
Lemma lem8055414 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term209 _143007 _143009 t y) (h2 : term223 _143007 _143008 _143009 f s x t y) : (term209 _143007 _143009 t y) = False.
Proof. exact (prop_ext (fun h3 : term209 _143007 _143009 t y => @lem8055409 _143007 _143008 _143009 f s x t y h1 h2) (fun h3 : False => @lem8055004 _143007 _143009 t y h1)). Qed.
Lemma lem8055415 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term209 _143007 _143009 t y) (h2 : term223 _143007 _143008 _143009 f s x t y) : False.
Proof. exact (EQ_MP (@lem8055414 _143007 _143008 _143009 f s x t y h1 h2) (@lem8055004 _143007 _143009 t y h1)). Qed.
Lemma lem8055416 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term209 _143007 _143008 s x) (h2 : term223 _143007 _143008 _143009 f s x t y) : (term209 _143007 _143008 s x) = False.
Proof. exact (prop_ext (fun h3 : term209 _143007 _143008 s x => @lem8055411 _143007 _143008 _143009 f s x t y h1 h2) (fun h3 : False => @lem8054975 _143007 _143008 s x h1)). Qed.
Lemma lem8055417 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term209 _143007 _143008 s x) (h2 : term223 _143007 _143008 _143009 f s x t y) : False.
Proof. exact (EQ_MP (@lem8055416 _143007 _143008 _143009 f s x t y h1 h2) (@lem8054975 _143007 _143008 s x h1)). Qed.
Lemma lem8055418 {_143007 _143008 _143009 : Type'} (x' : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : f x') (h2 : term215 _143007 _143008 _143009 t f s x y) : False.
Proof. exact (or_elim (@lem8054942 _143007 _143008 _143009 t f s x y h2) (fun h0 : term209 _143007 _143008 s x => @lem8055413 _143007 _143008 _143009 x' t f s x y h0 h1 h2) (fun h0 : term211 _143007 _143009 f t y => @lem8055399 _143007 _143008 _143009 t f s x y h0 h2)). Qed.
Lemma lem8055419 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (t : type24 _143007 _143009) (y : cart _143007 _143009) (h1 : term223 _143007 _143008 _143009 f s x t y) : False.
Proof. exact (or_elim (@lem8054935 _143007 _143008 _143009 f s x t y h1) (fun h0 : term209 _143007 _143008 s x => @lem8055417 _143007 _143008 _143009 f s x t y h0 h1) (fun h0 : term209 _143007 _143009 t y => @lem8055415 _143007 _143008 _143009 f s x t y h0 h1)). Qed.
Lemma lem8055420 {_143007 _143008 _143009 : Type'} (x' : type24 _143007 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : f x') (h2 : term197 _143007 _143008 _143009 t f s x y) : False.
Proof. exact (or_elim (@lem8054921 _143007 _143008 _143009 t f s x y h2) (fun h0 : term223 _143007 _143008 _143009 f s x t y => @lem8055419 _143007 _143008 _143009 f s x t y h0) (fun h0 : term215 _143007 _143008 _143009 t f s x y => @lem8055418 _143007 _143008 _143009 x' t f s x y h1 h0)). Qed.
Lemma lem8055421 {_143007 _143008 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term16 _143007 _143009 f) (h2 : term197 _143007 _143008 _143009 t f s x y) : False.
Proof. exact (ex_elim (@lem8054430 _143007 _143009 f h1) (fun x' : type24 _143007 _143009 => fun h0 : term76 _143007 _143009 f x' => @lem8055420 _143007 _143008 _143009 x' t f s x y h0 h2)). Qed.
Lemma lem8055422 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term16 _143007 _143009 f) (h2 : term68 _143007 _143008 _143009 f s x y) : False.
Proof. exact (ex_elim (@lem8054771 _143007 _143008 _143009 f s x y h2) (fun t : type24 _143007 _143009 => fun h0 : term199 _143007 _143008 _143009 f s x y t => @lem8055421 _143007 _143008 _143009 t f s x y h1 h0)). Qed.
Lemma lem8055423 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term16 _143007 _143009 f) (h2 : term68 _143007 _143008 _143009 f s x y) : (term68 _143007 _143008 _143009 f s x y) = False.
Proof. exact (prop_ext (fun h3 : term68 _143007 _143008 _143009 f s x y => @lem8055422 _143007 _143008 _143009 f s x y h1 h2) (fun h3 : False => @lem8054408 _143007 _143008 _143009 f s x y h2)). Qed.
Lemma lem8055424 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (h1 : term16 _143007 _143009 f) (h2 : term68 _143007 _143008 _143009 f s x y) : False.
Proof. exact (EQ_MP (@lem8055423 _143007 _143008 _143009 f s x y h1 h2) (@lem8054408 _143007 _143008 _143009 f s x y h2)). Qed.
Lemma lem8055425 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (f : type56 _143007 _143009) (h1 : term16 _143007 _143009 f) : term67 _143007 _143008 _143009 f s x y.
Proof. exact (fun h0 : term68 _143007 _143008 _143009 f s x y => @lem8055424 _143007 _143008 _143009 f s x y h1 h0). Qed.
Lemma lem8055426 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) (f : type56 _143007 _143009) (h1 : term16 _143007 _143009 f) : (term32 _143007 _143008 _143009 s x f y) = (term42 _143007 _143008 _143009 f s x y).
Proof. exact (EQ_MP (@lem8054407 _143007 _143008 _143009 f s x y) (@lem8055425 _143007 _143008 _143009 s x y f h1)). Qed.
Lemma lem8055431 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (x : cart _143007 _143008) (f : type56 _143007 _143009) (h1 : term16 _143007 _143009 f) : term46 _143007 _143008 _143009 f s x.
Proof. exact (fun y : cart _143007 _143009 => @lem8055426 _143007 _143008 _143009 s x y f h1). Qed.
Lemma lem8055436 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (f : type56 _143007 _143009) (h1 : term16 _143007 _143009 f) : term49 _143007 _143008 _143009 f s.
Proof. exact (fun x : cart _143007 _143008 => @lem8055431 _143007 _143008 _143009 s x f h1). Qed.
Lemma lem8055437 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : term50 _143007 _143008 _143009 f s.
Proof. exact (fun h0 : term16 _143007 _143009 f => @lem8055436 _143007 _143008 _143009 s f h0). Qed.
Lemma lem8055442 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) : term62 _143007 _143008 _143009 s.
Proof. exact (fun f : type56 _143007 _143009 => @lem8055437 _143007 _143008 _143009 f s). Qed.
Lemma lem8055447 {_143007 _143008 _143009 : Type'} : term66 _143007 _143008 _143009.
Proof. exact (fun s : type24 _143007 _143008 => @lem8055442 _143007 _143008 _143009 s). Qed.
Lemma lem8055448 {_143007 _143008 _143009 : Type'} : term65 _143007 _143008 _143009.
Proof. exact (EQ_MP (@lem8054402 _143007 _143008 _143009) (@lem8055447 _143007 _143008 _143009)). Qed.
Lemma lem8055449 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) : term251 _143007 _143008 _143009 s.
Proof. exact (@lem8055448 _143007 _143008 _143009 s). Qed.
Lemma lem8055450 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) : (term251 _143007 _143008 _143009 s) = (term61 _143007 _143008 _143009 s).
Proof. exact (eq_refl (term251 _143007 _143008 _143009 s)). Qed.
Lemma lem8055451 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) : term61 _143007 _143008 _143009 s.
Proof. exact (EQ_MP (@lem8055450 _143007 _143008 _143009 s) (@lem8055449 _143007 _143008 _143009 s)). Qed.
Lemma lem8055452 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (f : type56 _143007 _143009) : term252 _143007 _143008 _143009 s f.
Proof. exact (@lem8055451 _143007 _143008 _143009 s f). Qed.
Lemma lem8055453 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term252 _143007 _143008 _143009 s f) = (term52 _143007 _143008 _143009 f s).
Proof. exact (eq_refl (term252 _143007 _143008 _143009 s f)). Qed.
Lemma lem8055454 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : term52 _143007 _143008 _143009 f s.
Proof. exact (EQ_MP (@lem8055453 _143007 _143008 _143009 f s) (@lem8055452 _143007 _143008 _143009 s f)). Qed.
Lemma lem8055456 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : term52 _143007 _143008 _143009 f s.
Proof. exact (@lem8054233 _143007 _143008 _143009 f s (@lem8055454 _143007 _143008 _143009 f s)). Qed.
Lemma lem8055457 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (h1 : term53 _143007 _143008 _143009 f s) : False.
Proof. exact (@lem8055456 _143007 _143008 _143009 f s (@lem8054217 _143007 _143008 _143009 f s h1)). Qed.
Lemma lem8055458 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (h1 : term53 _143007 _143008 _143009 f s) : (term53 _143007 _143008 _143009 f s) = False.
Proof. exact (prop_ext (fun h2 : term53 _143007 _143008 _143009 f s => @lem8055457 _143007 _143008 _143009 f s h1) (fun h2 : False => @lem8054217 _143007 _143008 _143009 f s h1)). Qed.
Lemma lem8055459 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (h1 : term53 _143007 _143008 _143009 f s) : False.
Proof. exact (EQ_MP (@lem8055458 _143007 _143008 _143009 f s h1) (@lem8054217 _143007 _143008 _143009 f s h1)). Qed.
Lemma lem8055460 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : term52 _143007 _143008 _143009 f s.
Proof. exact (fun h0 : term53 _143007 _143008 _143009 f s => @lem8055459 _143007 _143008 _143009 f s h0). Qed.
Lemma lem8055461 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : term50 _143007 _143008 _143009 f s.
Proof. exact (EQ_MP (@lem8054216 _143007 _143008 _143009 f s) (@lem8055460 _143007 _143008 _143009 f s)). Qed.
Lemma lem8055462 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : term9 _143007 _143008 _143009 f s.
Proof. exact (EQ_MP (@lem8054212 _143007 _143008 _143009 f s) (@lem8055461 _143007 _143008 _143009 f s)). Qed.
Lemma lem8055463 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : term8 _143007 _143008 _143009 f s.
Proof. exact (EQ_MP (@lem8054067 _143007 _143008 _143009 f s) (@lem8055462 _143007 _143008 _143009 f s)). Qed.
Lemma lem8055464 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (f : type56 _143007 _143009) (h1 : term3 _143007 _143009 f) : term7 _143007 _143008 _143009 f s.
Proof. exact (@lem8055463 _143007 _143008 _143009 f s (@lem8049023 _143007 _143009 f h1)). Qed.
