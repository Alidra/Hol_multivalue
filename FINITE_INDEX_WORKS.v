Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_INDEX_WORKS_term_abbrevs.
Require Import CONJ_ASSOC_spec.
Require Import DISJ_ACI_spec.
Require Import IN_NUMSEG_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18393_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
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
Require Import thm21385_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Require Import thm7603491_spec.
Lemma lem7608077 (m : nat) (p : nat) (n : nat) (h1 : (term0 p m n) = (term1 m p n)) : (term0 p m n) = (term1 m p n).
Proof. exact (h1). Qed.
Lemma lem7608078 (m : nat) (p : nat) (n : nat) (h1 : (term0 p m n) = (term1 m p n)) : (term1 m p n) = (term0 p m n).
Proof. exact (SYM (@lem7608077 m p n h1)). Qed.
Lemma lem7608079 (p : nat) (m : nat) (n : nat) (h1 : (term1 m p n) = (term0 p m n)) : (term1 m p n) = (term0 p m n).
Proof. exact (h1). Qed.
Lemma lem7608080 (p : nat) (m : nat) (n : nat) (h1 : (term1 m p n) = (term0 p m n)) : (term0 p m n) = (term1 m p n).
Proof. exact (SYM (@lem7608079 p m n h1)). Qed.
Lemma lem7608081 (p : nat) (m : nat) (n : nat) : ((term0 p m n) = (term1 m p n)) = ((term1 m p n) = (term0 p m n)).
Proof. exact (prop_ext (fun h1 : (term0 p m n) = (term1 m p n) => @lem7608078 m p n h1) (fun h1 : (term1 m p n) = (term0 p m n) => @lem7608080 p m n h1)). Qed.
Lemma lem7608082 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (fun_ext (fun p : nat => @lem7608081 p m n)). Qed.
Lemma lem7608083 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7608084 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem7608083) (@lem7608082 m n)). Qed.
Lemma lem7608085 (m : nat) : (term6 m) = (term7 m).
Proof. exact (fun_ext (fun n : nat => @lem7608084 m n)). Qed.
Lemma lem7608086 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7608087 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem7608086) (@lem7608085 m)). Qed.
Lemma lem7608088 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem7608087 m)). Qed.
Lemma lem7608089 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7608090 : term12 = term13.
Proof. exact (MK_COMB (@lem7608089) (@lem7608088)). Qed.
Lemma lem7608091 : term13.
Proof. exact (EQ_MP (@lem7608090) (@lem5371273)). Qed.
Lemma lem7608092 (m : nat) : term14 m.
Proof. exact (@lem7608091 m). Qed.
Lemma lem7608093 (m : nat) : (term14 m) = (term9 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem7608094 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem7608093 m) (@lem7608092 m)). Qed.
Lemma lem7608095 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem7608094 m n). Qed.
Lemma lem7608096 (m : nat) (n : nat) : (term15 m n) = (term5 m n).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem7608097 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem7608096 m n) (@lem7608095 m n)). Qed.
Lemma lem7608098 (m : nat) (n : nat) (p : nat) : term16 m n p.
Proof. exact (@lem7608097 m n p). Qed.
Lemma lem7608099 (p : nat) (m : nat) (n : nat) : (term16 m n p) = ((term1 m p n) = (term0 p m n)).
Proof. exact (eq_refl (term16 m n p)). Qed.
Lemma lem7608101 (t1 : Prop) : term17 t1.
Proof. exact (@lem512 t1). Qed.
Lemma lem7608102 (t1 : Prop) : (term17 t1) = (term18 t1).
Proof. exact (eq_refl (term17 t1)). Qed.
Lemma lem7608103 (t1 : Prop) : term18 t1.
Proof. exact (EQ_MP (@lem7608102 t1) (@lem7608101 t1)). Qed.
Lemma lem7608104 (t1 : Prop) (t2 : Prop) : term19 t1 t2.
Proof. exact (@lem7608103 t1 t2). Qed.
Lemma lem7608105 (t1 : Prop) (t2 : Prop) : (term19 t1 t2) = (term20 t1 t2).
Proof. exact (eq_refl (term19 t1 t2)). Qed.
Lemma lem7608106 (t1 : Prop) (t2 : Prop) : term20 t1 t2.
Proof. exact (EQ_MP (@lem7608105 t1 t2) (@lem7608104 t1 t2)). Qed.
Lemma lem7608107 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term21 t1 t2 t3.
Proof. exact (@lem7608106 t1 t2 t3). Qed.
Lemma lem7608108 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term21 t1 t2 t3) = ((term22 t1 t2 t3) = (term23 t1 t2 t3)).
Proof. exact (eq_refl (term21 t1 t2 t3)). Qed.
Lemma lem7608115 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term22 t1 t2 t3) = (term23 t1 t2 t3).
Proof. exact (EQ_MP (@lem7608108 t1 t2 t3) (@lem7608107 t1 t2 t3)). Qed.
Lemma lem7608116 {A : Type'} (n : nat) (i : finite_image A) : (term24 A n i) = (term25 A n i).
Proof. exact (@lem7608115 (term26 n) (term27 A n) ((@finite_index A n) = i)). Qed.
Lemma lem7608120 (p : nat) (m : nat) (n : nat) : (term1 m p n) = (term0 p m n).
Proof. exact (EQ_MP (@lem7608099 p m n) (@lem7608098 m n p)). Qed.
Lemma lem7608121 {A : Type'} (n : nat) : (term28 A n) = (term29 A n).
Proof. exact (@lem7608120 n term30 (@dimindex A (@UNIV A))). Qed.
Lemma lem7608122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7608123 {A : Type'} (n : nat) : (term31 A n) = (term32 A n).
Proof. exact (MK_COMB (@lem7608122) (@lem7608121 A n)). Qed.
Lemma lem7608126 {A : Type'} (n : nat) (i : finite_image A) : ((@finite_index A n) = i) = ((@finite_index A n) = i).
Proof. exact (eq_refl ((@finite_index A n) = i)). Qed.
Lemma lem7608127 {A : Type'} (n : nat) (i : finite_image A) : (term25 A n i) = (term33 A n i).
Proof. exact (MK_COMB (@lem7608123 A n) (@lem7608126 A n i)). Qed.
Lemma lem7608130 {A : Type'} (n : nat) (i : finite_image A) : (term24 A n i) = (term33 A n i).
Proof. exact (TRANS (@lem7608116 A n i) (@lem7608127 A n i)). Qed.
Lemma lem7608131 {A : Type'} (i : finite_image A) : (term34 A i) = (term35 A i).
Proof. exact (fun_ext (fun n : nat => @lem7608130 A n i)). Qed.
Lemma lem7608132 : (@ex1 nat) = (@ex1 nat).
Proof. exact (eq_refl (@ex1 nat)). Qed.
Lemma lem7608133 {A : Type'} (i : finite_image A) : (term36 A i) = (term37 A i).
Proof. exact (MK_COMB (@lem7608132) (@lem7608131 A i)). Qed.
Lemma lem7608134 {A : Type'} : (term38 A) = (term39 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7608133 A i)). Qed.
Lemma lem7608135 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7608136 {A : Type'} : (term40 A) = (term41 A).
Proof. exact (MK_COMB (@lem7608135 A) (@lem7608134 A)). Qed.
Lemma lem7608141 {A : Type'} : (term41 A) = (term40 A).
Proof. exact (SYM (@lem7608136 A)). Qed.
Lemma lem7608143 (p : Prop) : p = (term42 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7608144 {A : Type'} : (term41 A) = (term43 A).
Proof. exact (@lem7608143 (term41 A)). Qed.
Lemma lem7608145 {A : Type'} : (term43 A) = (term41 A).
Proof. exact (SYM (@lem7608144 A)). Qed.
Lemma lem7608146 {A : Type'} (h1 : term44 A) : term44 A.
Proof. exact (h1). Qed.
Lemma lem7608147 {A : Type'} : term45 A.
Proof. exact (@lem7603491 A). Qed.
Lemma lem7608153 {A : Type'} (h1 : term46 A) : term46 A.
Proof. exact (h1). Qed.
Lemma lem7608154 {A : Type'} : term47 A.
Proof. exact (fun h0 : term46 A => @lem7608153 A h0). Qed.
Lemma lem7608155 {A : Type'} (h1 : term47 A) : term47 A.
Proof. exact (h1). Qed.
Lemma lem7608156 {A : Type'} (h1 : term46 A) : term46 A.
Proof. exact (h1). Qed.
Lemma lem7608157 {A : Type'} (h1 : term46 A) (h2 : term47 A) : term46 A.
Proof. exact (@lem7608155 A h2 (@lem7608156 A h1)). Qed.
Lemma lem7608158 {A : Type'} (h1 : term46 A) : term48 A.
Proof. exact (fun h0 : term47 A => @lem7608157 A h1 h0). Qed.
Lemma lem7608159 {A : Type'} (h1 : term47 A) : term47 A.
Proof. exact (h1). Qed.
Lemma lem7608160 {A : Type'} (h1 : term46 A) (h2 : term47 A) : term46 A.
Proof. exact (@lem7608158 A h1 (@lem7608159 A h2)). Qed.
Lemma lem7608161 {A : Type'} (h1 : term47 A) : term47 A.
Proof. exact (fun h0 : term46 A => @lem7608160 A h0 h1). Qed.
Lemma lem7608162 {A : Type'} : term49 A.
Proof. exact (fun h0 : term47 A => @lem7608161 A h0). Qed.
Lemma lem7608165 {A : Type'} : term47 A.
Proof. exact (@lem7608162 A (@lem7608154 A)). Qed.
Lemma lem7608166 {A : Type'} : term47 A.
Proof. exact (@lem7608165 A). Qed.
Lemma lem7608176 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7608177 {A : Type'} : (term50 A) = (term51 A).
Proof. exact (@lem7608176 (term45 A)). Qed.
Lemma lem7608188 {A : Type'} : (term52 A) = (term52 A).
Proof. exact (eq_refl (term52 A)). Qed.
Lemma lem7608195 {A : Type'} : (term46 A) = (term53 A).
Proof. exact (MK_COMB (@lem7608188 A) (@lem7608177 A)). Qed.
Lemma lem7608200 {A : Type'} (r : nat) : ((term29 A r) = ((term54 A r) = r)) = ((term29 A r) = ((term54 A r) = r)).
Proof. exact (eq_refl ((term29 A r) = ((term54 A r) = r))). Qed.
Lemma lem7608201 {A : Type'} : (term55 A) = (term55 A).
Proof. exact (fun_ext (fun r : nat => @lem7608200 A r)). Qed.
Lemma lem7608202 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7608203 {A : Type'} : (term56 A) = (term56 A).
Proof. exact (MK_COMB (@lem7608202) (@lem7608201 A)). Qed.
Lemma lem7608204 {A : Type'} (a : finite_image A) : ((term57 A a) = a) = ((term57 A a) = a).
Proof. exact (eq_refl ((term57 A a) = a)). Qed.
Lemma lem7608205 {A : Type'} : (term58 A) = (term58 A).
Proof. exact (fun_ext (fun a : finite_image A => @lem7608204 A a)). Qed.
Lemma lem7608206 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7608207 {A : Type'} : (term59 A) = (term59 A).
Proof. exact (MK_COMB (@lem7608206 A) (@lem7608205 A)). Qed.
Lemma lem7608208 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7608209 {A : Type'} : (term60 A) = (term60 A).
Proof. exact (MK_COMB (@lem7608208) (@lem7608207 A)). Qed.
Lemma lem7608210 {A : Type'} : (term45 A) = (term45 A).
Proof. exact (MK_COMB (@lem7608209 A) (@lem7608203 A)). Qed.
Lemma lem7608211 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7608212 {A : Type'} : (term51 A) = (term51 A).
Proof. exact (MK_COMB (@lem7608211) (@lem7608210 A)). Qed.
Lemma lem7608217 {A : Type'} (n : nat) (i : finite_image A) : (term33 A n i) = (term33 A n i).
Proof. exact (eq_refl (term33 A n i)). Qed.
Lemma lem7608218 {A : Type'} (i : finite_image A) : (term35 A i) = (term35 A i).
Proof. exact (fun_ext (fun n : nat => @lem7608217 A n i)). Qed.
Lemma lem7608219 : (@ex1 nat) = (@ex1 nat).
Proof. exact (eq_refl (@ex1 nat)). Qed.
Lemma lem7608220 {A : Type'} (i : finite_image A) : (term37 A i) = (term37 A i).
Proof. exact (MK_COMB (@lem7608219) (@lem7608218 A i)). Qed.
Lemma lem7608221 {A : Type'} : (term39 A) = (term39 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7608220 A i)). Qed.
Lemma lem7608222 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7608223 {A : Type'} : (term41 A) = (term41 A).
Proof. exact (MK_COMB (@lem7608222 A) (@lem7608221 A)). Qed.
Lemma lem7608224 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7608225 {A : Type'} : (term44 A) = (term44 A).
Proof. exact (MK_COMB (@lem7608224) (@lem7608223 A)). Qed.
Lemma lem7608226 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7608227 {A : Type'} : (term52 A) = (term52 A).
Proof. exact (MK_COMB (@lem7608226) (@lem7608225 A)). Qed.
Lemma lem7608228 {A : Type'} : (term53 A) = (term53 A).
Proof. exact (MK_COMB (@lem7608227 A) (@lem7608212 A)). Qed.
Lemma lem7608255 {A : Type'} : (term46 A) = (term53 A).
Proof. exact (TRANS (@lem7608195 A) (@lem7608228 A)). Qed.
Lemma lem7608256 {A : Type'} : (term53 A) = (term46 A).
Proof. exact (SYM (@lem7608255 A)). Qed.
Lemma lem7608257 {A : Type'} (h1 : term44 A) : term44 A.
Proof. exact (h1). Qed.
Lemma lem7608258 {A : Type'} (h1 : term45 A) : term45 A.
Proof. exact (h1). Qed.
Lemma lem7608267 {A : Type'} (n : nat) (i : finite_image A) : (term61 A n i) = (term62 A n i).
Proof. exact (@lem17045 (term29 A n) ((@finite_index A n) = i)). Qed.
Lemma lem7608270 {A : Type'} (n : nat) (i : finite_image A) : (term33 A n i) = (term33 A n i).
Proof. exact (eq_refl (term33 A n i)). Qed.
Lemma lem7608271 (n' : nat) (n : nat) : (term63 n' n) = (term63 n' n).
Proof. exact (eq_refl (term63 n' n)). Qed.
Lemma lem7608273 {A : Type'} (n : nat) (i : finite_image A) : (term64 A i n) = (term33 A n i).
Proof. exact (eq_refl (term64 A i n)). Qed.
Lemma lem7608274 {A : Type'} (n' : nat) (i : finite_image A) : (term64 A i n') = (term33 A n' i).
Proof. exact (eq_refl (term64 A i n')). Qed.
Lemma lem7608275 {A : Type'} (n' : nat) (i : finite_image A) : (term33 A n' i) = (term33 A n' i).
Proof. exact (@lem7608270 A n' i). Qed.
Lemma lem7608276 (P : nat -> Prop) : (term65 P) = (term66 P).
Proof. exact (@lem18393 nat P). Qed.
Lemma lem7608277 {A : Type'} (i : finite_image A) : (term67 A i) = (term68 A i).
Proof. exact (@lem7608276 (term35 A i)). Qed.
Lemma lem7608278 {A : Type'} (n' : nat) (i : finite_image A) : (term64 A i n') = (term33 A n' i).
Proof. exact (TRANS (@lem7608274 A n' i) (@lem7608275 A n' i)). Qed.
Lemma lem7608279 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7608280 {A : Type'} (n' : nat) (i : finite_image A) : (term69 A i n') = (term70 A n' i).
Proof. exact (MK_COMB (@lem7608279) (@lem7608278 A n' i)). Qed.
Lemma lem7608281 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term71 A i n' n) = (term72 A i n' n).
Proof. exact (MK_COMB (@lem7608280 A n' i) (@lem7608271 n' n)). Qed.
Lemma lem7608282 {A : Type'} (n : nat) (i : finite_image A) : (term64 A i n) = (term33 A n i).
Proof. exact (eq_refl (term64 A i n)). Qed.
Lemma lem7608283 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7608284 {A : Type'} (n : nat) (i : finite_image A) : (term69 A i n) = (term70 A n i).
Proof. exact (MK_COMB (@lem7608283) (@lem7608282 A n i)). Qed.
Lemma lem7608285 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term73 A i n' n) = (term74 A i n' n).
Proof. exact (MK_COMB (@lem7608284 A n i) (@lem7608281 A i n' n)). Qed.
Lemma lem7608286 {A : Type'} (i : finite_image A) (n : nat) : (term75 A i n) = (term76 A i n).
Proof. exact (fun_ext (fun n' : nat => @lem7608285 A i n' n)). Qed.
Lemma lem7608287 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7608288 {A : Type'} (i : finite_image A) (n : nat) : (term77 A i n) = (term78 A i n).
Proof. exact (MK_COMB (@lem7608287) (@lem7608286 A i n)). Qed.
Lemma lem7608289 {A : Type'} (i : finite_image A) : (term79 A i) = (term80 A i).
Proof. exact (fun_ext (fun n : nat => @lem7608288 A i n)). Qed.
Lemma lem7608290 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7608291 {A : Type'} (i : finite_image A) : (term81 A i) = (term82 A i).
Proof. exact (MK_COMB (@lem7608290) (@lem7608289 A i)). Qed.
Lemma lem7608292 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7608293 {A : Type'} (n : nat) (i : finite_image A) : (term83 A i n) = (term61 A n i).
Proof. exact (MK_COMB (@lem7608292) (@lem7608273 A n i)). Qed.
Lemma lem7608294 {A : Type'} (n : nat) (i : finite_image A) : (term83 A i n) = (term62 A n i).
Proof. exact (TRANS (@lem7608293 A n i) (@lem7608267 A n i)). Qed.
Lemma lem7608295 {A : Type'} (i : finite_image A) : (term84 A i) = (term85 A i).
Proof. exact (fun_ext (fun n : nat => @lem7608294 A n i)). Qed.
Lemma lem7608296 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7608297 {A : Type'} (i : finite_image A) : (term86 A i) = (term87 A i).
Proof. exact (MK_COMB (@lem7608296) (@lem7608295 A i)). Qed.
Lemma lem7608298 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7608299 {A : Type'} (i : finite_image A) : (term88 A i) = (term89 A i).
Proof. exact (MK_COMB (@lem7608298) (@lem7608297 A i)). Qed.
Lemma lem7608300 {A : Type'} (i : finite_image A) : (term68 A i) = (term90 A i).
Proof. exact (MK_COMB (@lem7608299 A i) (@lem7608291 A i)). Qed.
Lemma lem7608301 {A : Type'} (i : finite_image A) : (term67 A i) = (term90 A i).
Proof. exact (TRANS (@lem7608277 A i) (@lem7608300 A i)). Qed.
Lemma lem7608302 {A : Type'} (P : type33 A) : (term91 A P) = (term92 A P).
Proof. exact (@lem18392 (finite_image A) P). Qed.
Lemma lem7608303 {A : Type'} : (term44 A) = (term93 A).
Proof. exact (@lem7608302 A (term39 A)). Qed.
Lemma lem7608304 {A : Type'} (i : finite_image A) : (term94 A i) = (term37 A i).
Proof. exact (eq_refl (term94 A i)). Qed.
Lemma lem7608305 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7608306 {A : Type'} (i : finite_image A) : (term95 A i) = (term67 A i).
Proof. exact (MK_COMB (@lem7608305) (@lem7608304 A i)). Qed.
Lemma lem7608307 {A : Type'} (i : finite_image A) : (term95 A i) = (term90 A i).
Proof. exact (TRANS (@lem7608306 A i) (@lem7608301 A i)). Qed.
Lemma lem7608308 {A : Type'} : (term96 A) = (term97 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7608307 A i)). Qed.
Lemma lem7608309 {A : Type'} : (@ex (finite_image A)) = (@ex (finite_image A)).
Proof. exact (eq_refl (@ex (finite_image A))). Qed.
Lemma lem7608310 {A : Type'} : (term93 A) = (term98 A).
Proof. exact (MK_COMB (@lem7608309 A) (@lem7608308 A)). Qed.
Lemma lem7608311 {A : Type'} : (term44 A) = (term98 A).
Proof. exact (TRANS (@lem7608303 A) (@lem7608310 A)). Qed.
Lemma lem7608313 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term99 A P Q) = (term100 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem7608314 {A : Type'} (P : type33 A) (Q : type33 A) : (term101 A P Q) = (term102 A P Q).
Proof. exact (@lem7608313 (finite_image A) P Q). Qed.
Lemma lem7608315 {A : Type'} : (term103 A) = (term104 A).
Proof. exact (@lem7608314 A (term105 A) (term106 A)). Qed.
Lemma lem7608316 {A : Type'} (i : finite_image A) : (term107 A i) = (term87 A i).
Proof. exact (eq_refl (term107 A i)). Qed.
Lemma lem7608317 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7608318 {A : Type'} (i : finite_image A) : (term108 A i) = (term89 A i).
Proof. exact (MK_COMB (@lem7608317) (@lem7608316 A i)). Qed.
Lemma lem7608319 {A : Type'} (i : finite_image A) : (term109 A i) = (term82 A i).
Proof. exact (eq_refl (term109 A i)). Qed.
Lemma lem7608320 {A : Type'} (i : finite_image A) : (term110 A i) = (term90 A i).
Proof. exact (MK_COMB (@lem7608318 A i) (@lem7608319 A i)). Qed.
Lemma lem7608321 {A : Type'} : (term111 A) = (term97 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7608320 A i)). Qed.
Lemma lem7608322 {A : Type'} : (@ex (finite_image A)) = (@ex (finite_image A)).
Proof. exact (eq_refl (@ex (finite_image A))). Qed.
Lemma lem7608323 {A : Type'} : (term103 A) = (term98 A).
Proof. exact (MK_COMB (@lem7608322 A) (@lem7608321 A)). Qed.
Lemma lem7608324 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7608325 {A : Type'} : (term112 A) = (term113 A).
Proof. exact (MK_COMB (@lem7608324) (@lem7608323 A)). Qed.
Lemma lem7608326 {A : Type'} (i : finite_image A) : (term107 A i) = (term87 A i).
Proof. exact (eq_refl (term107 A i)). Qed.
Lemma lem7608327 {A : Type'} : (term114 A) = (term105 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7608326 A i)). Qed.
Lemma lem7608328 {A : Type'} : (@ex (finite_image A)) = (@ex (finite_image A)).
Proof. exact (eq_refl (@ex (finite_image A))). Qed.
Lemma lem7608329 {A : Type'} : (term115 A) = (term116 A).
Proof. exact (MK_COMB (@lem7608328 A) (@lem7608327 A)). Qed.
Lemma lem7608330 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7608331 {A : Type'} : (term117 A) = (term118 A).
Proof. exact (MK_COMB (@lem7608330) (@lem7608329 A)). Qed.
Lemma lem7608332 {A : Type'} (i : finite_image A) : (term109 A i) = (term82 A i).
Proof. exact (eq_refl (term109 A i)). Qed.
Lemma lem7608333 {A : Type'} : (term119 A) = (term106 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7608332 A i)). Qed.
Lemma lem7608334 {A : Type'} : (@ex (finite_image A)) = (@ex (finite_image A)).
Proof. exact (eq_refl (@ex (finite_image A))). Qed.
Lemma lem7608335 {A : Type'} : (term120 A) = (term121 A).
Proof. exact (MK_COMB (@lem7608334 A) (@lem7608333 A)). Qed.
Lemma lem7608336 {A : Type'} : (term104 A) = (term122 A).
Proof. exact (MK_COMB (@lem7608331 A) (@lem7608335 A)). Qed.
Lemma lem7608337 {A : Type'} : ((term103 A) = (term104 A)) = ((term98 A) = (term122 A)).
Proof. exact (MK_COMB (@lem7608325 A) (@lem7608336 A)). Qed.
Lemma lem7608338 {A : Type'} : (term98 A) = (term122 A).
Proof. exact (EQ_MP (@lem7608337 A) (@lem7608315 A)). Qed.
Lemma lem7608400 {A : Type'} (P : Prop) (Q : A -> Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem7608401 (P : Prop) (Q : nat -> Prop) : (term125 P Q) = (term126 P Q).
Proof. exact (@lem7608400 nat P Q). Qed.
Lemma lem7608402 {A : Type'} (i : finite_image A) (n : nat) : (term127 A i n) = (term128 A i n).
Proof. exact (@lem7608401 (term33 A n i) (term129 A i n)). Qed.
Lemma lem7608403 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term130 A i n n') = (term72 A i n' n).
Proof. exact (eq_refl (term130 A i n n')). Qed.
Lemma lem7608404 {A : Type'} (n : nat) (i : finite_image A) : (term70 A n i) = (term70 A n i).
Proof. exact (eq_refl (term70 A n i)). Qed.
Lemma lem7608405 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term131 A i n n') = (term74 A i n' n).
Proof. exact (MK_COMB (@lem7608404 A n i) (@lem7608403 A i n' n)). Qed.
Lemma lem7608406 {A : Type'} (i : finite_image A) (n : nat) : (term132 A i n) = (term76 A i n).
Proof. exact (fun_ext (fun n' : nat => @lem7608405 A i n' n)). Qed.
Lemma lem7608407 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7608408 {A : Type'} (i : finite_image A) (n : nat) : (term127 A i n) = (term78 A i n).
Proof. exact (MK_COMB (@lem7608407) (@lem7608406 A i n)). Qed.
Lemma lem7608409 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7608410 {A : Type'} (i : finite_image A) (n : nat) : (term133 A i n) = (term134 A i n).
Proof. exact (MK_COMB (@lem7608409) (@lem7608408 A i n)). Qed.
Lemma lem7608411 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term130 A i n n') = (term72 A i n' n).
Proof. exact (eq_refl (term130 A i n n')). Qed.
Lemma lem7608412 {A : Type'} (i : finite_image A) (n : nat) : (term135 A i n) = (term129 A i n).
Proof. exact (fun_ext (fun n' : nat => @lem7608411 A i n' n)). Qed.
Lemma lem7608413 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7608414 {A : Type'} (i : finite_image A) (n : nat) : (term136 A i n) = (term137 A i n).
Proof. exact (MK_COMB (@lem7608413) (@lem7608412 A i n)). Qed.
Lemma lem7608415 {A : Type'} (n : nat) (i : finite_image A) : (term70 A n i) = (term70 A n i).
Proof. exact (eq_refl (term70 A n i)). Qed.
Lemma lem7608416 {A : Type'} (i : finite_image A) (n : nat) : (term128 A i n) = (term138 A i n).
Proof. exact (MK_COMB (@lem7608415 A n i) (@lem7608414 A i n)). Qed.
Lemma lem7608417 {A : Type'} (i : finite_image A) (n : nat) : ((term127 A i n) = (term128 A i n)) = ((term78 A i n) = (term138 A i n)).
Proof. exact (MK_COMB (@lem7608410 A i n) (@lem7608416 A i n)). Qed.
Lemma lem7608418 {A : Type'} (i : finite_image A) (n : nat) : (term78 A i n) = (term138 A i n).
Proof. exact (EQ_MP (@lem7608417 A i n) (@lem7608402 A i n)). Qed.
Lemma lem7608467 {A : Type'} (i : finite_image A) : (term80 A i) = (term139 A i).
Proof. exact (fun_ext (fun n : nat => @lem7608418 A i n)). Qed.
Lemma lem7608468 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7608469 {A : Type'} (i : finite_image A) : (term82 A i) = (term140 A i).
Proof. exact (MK_COMB (@lem7608468) (@lem7608467 A i)). Qed.
Lemma lem7608518 {A : Type'} : (term106 A) = (term141 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7608469 A i)). Qed.
Lemma lem7608519 {A : Type'} : (@ex (finite_image A)) = (@ex (finite_image A)).
Proof. exact (eq_refl (@ex (finite_image A))). Qed.
Lemma lem7608520 {A : Type'} : (term121 A) = (term142 A).
Proof. exact (MK_COMB (@lem7608519 A) (@lem7608518 A)). Qed.
Lemma lem7608525 {A : Type'} : (term118 A) = (term118 A).
Proof. exact (eq_refl (term118 A)). Qed.
Lemma lem7608526 {A : Type'} : (term122 A) = (term143 A).
Proof. exact (MK_COMB (@lem7608525 A) (@lem7608520 A)). Qed.
Lemma lem7608527 {A : Type'} : (term98 A) = (term143 A).
Proof. exact (TRANS (@lem7608338 A) (@lem7608526 A)). Qed.
Lemma lem7608529 {A : Type'} (P : Prop) (Q : A -> Prop) : (term124 A P Q) = (term123 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7608530 (P : Prop) (Q : nat -> Prop) : (term126 P Q) = (term125 P Q).
Proof. exact (@lem7608529 nat P Q). Qed.
Lemma lem7608531 {A : Type'} (i : finite_image A) (n : nat) : (term128 A i n) = (term127 A i n).
Proof. exact (@lem7608530 (term33 A n i) (term129 A i n)). Qed.
Lemma lem7608532 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term130 A i n n') = (term72 A i n' n).
Proof. exact (eq_refl (term130 A i n n')). Qed.
Lemma lem7608533 {A : Type'} (i : finite_image A) (n : nat) : (term135 A i n) = (term129 A i n).
Proof. exact (fun_ext (fun n' : nat => @lem7608532 A i n' n)). Qed.
Lemma lem7608534 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7608535 {A : Type'} (i : finite_image A) (n : nat) : (term136 A i n) = (term137 A i n).
Proof. exact (MK_COMB (@lem7608534) (@lem7608533 A i n)). Qed.
Lemma lem7608536 {A : Type'} (n : nat) (i : finite_image A) : (term70 A n i) = (term70 A n i).
Proof. exact (eq_refl (term70 A n i)). Qed.
Lemma lem7608537 {A : Type'} (i : finite_image A) (n : nat) : (term128 A i n) = (term138 A i n).
Proof. exact (MK_COMB (@lem7608536 A n i) (@lem7608535 A i n)). Qed.
Lemma lem7608538 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7608539 {A : Type'} (i : finite_image A) (n : nat) : (term144 A i n) = (term145 A i n).
Proof. exact (MK_COMB (@lem7608538) (@lem7608537 A i n)). Qed.
Lemma lem7608540 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term130 A i n n') = (term72 A i n' n).
Proof. exact (eq_refl (term130 A i n n')). Qed.
Lemma lem7608541 {A : Type'} (n : nat) (i : finite_image A) : (term70 A n i) = (term70 A n i).
Proof. exact (eq_refl (term70 A n i)). Qed.
Lemma lem7608542 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term131 A i n n') = (term74 A i n' n).
Proof. exact (MK_COMB (@lem7608541 A n i) (@lem7608540 A i n' n)). Qed.
Lemma lem7608543 {A : Type'} (i : finite_image A) (n : nat) : (term132 A i n) = (term76 A i n).
Proof. exact (fun_ext (fun n' : nat => @lem7608542 A i n' n)). Qed.
Lemma lem7608544 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7608545 {A : Type'} (i : finite_image A) (n : nat) : (term127 A i n) = (term78 A i n).
Proof. exact (MK_COMB (@lem7608544) (@lem7608543 A i n)). Qed.
Lemma lem7608546 {A : Type'} (i : finite_image A) (n : nat) : ((term128 A i n) = (term127 A i n)) = ((term138 A i n) = (term78 A i n)).
Proof. exact (MK_COMB (@lem7608539 A i n) (@lem7608545 A i n)). Qed.
Lemma lem7608547 {A : Type'} (i : finite_image A) (n : nat) : (term138 A i n) = (term78 A i n).
Proof. exact (EQ_MP (@lem7608546 A i n) (@lem7608531 A i n)). Qed.
Lemma lem7608548 {A : Type'} (i : finite_image A) : (term139 A i) = (term80 A i).
Proof. exact (fun_ext (fun n : nat => @lem7608547 A i n)). Qed.
Lemma lem7608549 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7608550 {A : Type'} (i : finite_image A) : (term140 A i) = (term82 A i).
Proof. exact (MK_COMB (@lem7608549) (@lem7608548 A i)). Qed.
Lemma lem7608551 {A : Type'} : (term141 A) = (term106 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7608550 A i)). Qed.
Lemma lem7608552 {A : Type'} : (@ex (finite_image A)) = (@ex (finite_image A)).
Proof. exact (eq_refl (@ex (finite_image A))). Qed.
Lemma lem7608553 {A : Type'} : (term142 A) = (term121 A).
Proof. exact (MK_COMB (@lem7608552 A) (@lem7608551 A)). Qed.
Lemma lem7608554 {A : Type'} : (term118 A) = (term118 A).
Proof. exact (eq_refl (term118 A)). Qed.
Lemma lem7608555 {A : Type'} : (term143 A) = (term122 A).
Proof. exact (MK_COMB (@lem7608554 A) (@lem7608553 A)). Qed.
Lemma lem7608557 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term100 A P Q) = (term99 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem7608558 {A : Type'} (P : type33 A) (Q : type33 A) : (term102 A P Q) = (term101 A P Q).
Proof. exact (@lem7608557 (finite_image A) P Q). Qed.
Lemma lem7608559 {A : Type'} : (term104 A) = (term103 A).
Proof. exact (@lem7608558 A (term105 A) (term106 A)). Qed.
Lemma lem7608560 {A : Type'} (i : finite_image A) : (term107 A i) = (term87 A i).
Proof. exact (eq_refl (term107 A i)). Qed.
Lemma lem7608561 {A : Type'} : (term114 A) = (term105 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7608560 A i)). Qed.
Lemma lem7608562 {A : Type'} : (@ex (finite_image A)) = (@ex (finite_image A)).
Proof. exact (eq_refl (@ex (finite_image A))). Qed.
Lemma lem7608563 {A : Type'} : (term115 A) = (term116 A).
Proof. exact (MK_COMB (@lem7608562 A) (@lem7608561 A)). Qed.
Lemma lem7608564 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7608565 {A : Type'} : (term117 A) = (term118 A).
Proof. exact (MK_COMB (@lem7608564) (@lem7608563 A)). Qed.
Lemma lem7608566 {A : Type'} (i : finite_image A) : (term109 A i) = (term82 A i).
Proof. exact (eq_refl (term109 A i)). Qed.
Lemma lem7608567 {A : Type'} : (term119 A) = (term106 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7608566 A i)). Qed.
Lemma lem7608568 {A : Type'} : (@ex (finite_image A)) = (@ex (finite_image A)).
Proof. exact (eq_refl (@ex (finite_image A))). Qed.
Lemma lem7608569 {A : Type'} : (term120 A) = (term121 A).
Proof. exact (MK_COMB (@lem7608568 A) (@lem7608567 A)). Qed.
Lemma lem7608570 {A : Type'} : (term104 A) = (term122 A).
Proof. exact (MK_COMB (@lem7608565 A) (@lem7608569 A)). Qed.
Lemma lem7608571 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7608572 {A : Type'} : (term146 A) = (term147 A).
Proof. exact (MK_COMB (@lem7608571) (@lem7608570 A)). Qed.
Lemma lem7608573 {A : Type'} (i : finite_image A) : (term107 A i) = (term87 A i).
Proof. exact (eq_refl (term107 A i)). Qed.
Lemma lem7608574 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7608575 {A : Type'} (i : finite_image A) : (term108 A i) = (term89 A i).
Proof. exact (MK_COMB (@lem7608574) (@lem7608573 A i)). Qed.
Lemma lem7608576 {A : Type'} (i : finite_image A) : (term109 A i) = (term82 A i).
Proof. exact (eq_refl (term109 A i)). Qed.
Lemma lem7608577 {A : Type'} (i : finite_image A) : (term110 A i) = (term90 A i).
Proof. exact (MK_COMB (@lem7608575 A i) (@lem7608576 A i)). Qed.
Lemma lem7608578 {A : Type'} : (term111 A) = (term97 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7608577 A i)). Qed.
Lemma lem7608579 {A : Type'} : (@ex (finite_image A)) = (@ex (finite_image A)).
Proof. exact (eq_refl (@ex (finite_image A))). Qed.
Lemma lem7608580 {A : Type'} : (term103 A) = (term98 A).
Proof. exact (MK_COMB (@lem7608579 A) (@lem7608578 A)). Qed.
Lemma lem7608581 {A : Type'} : ((term104 A) = (term103 A)) = ((term122 A) = (term98 A)).
Proof. exact (MK_COMB (@lem7608572 A) (@lem7608580 A)). Qed.
Lemma lem7608582 {A : Type'} : (term122 A) = (term98 A).
Proof. exact (EQ_MP (@lem7608581 A) (@lem7608559 A)). Qed.
Lemma lem7608584 {A : Type'} (P : Prop) (Q : A -> Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7608585 (P : Prop) (Q : nat -> Prop) : (term150 P Q) = (term151 P Q).
Proof. exact (@lem7608584 nat P Q). Qed.
Lemma lem7608586 {A : Type'} (i : finite_image A) : (term152 A i) = (term153 A i).
Proof. exact (@lem7608585 (term87 A i) (term80 A i)). Qed.
Lemma lem7608587 {A : Type'} (i : finite_image A) (n : nat) : (term154 A i n) = (term78 A i n).
Proof. exact (eq_refl (term154 A i n)). Qed.
Lemma lem7608588 {A : Type'} (i : finite_image A) : (term155 A i) = (term80 A i).
Proof. exact (fun_ext (fun n : nat => @lem7608587 A i n)). Qed.
Lemma lem7608589 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7608590 {A : Type'} (i : finite_image A) : (term156 A i) = (term82 A i).
Proof. exact (MK_COMB (@lem7608589) (@lem7608588 A i)). Qed.
Lemma lem7608591 {A : Type'} (i : finite_image A) : (term89 A i) = (term89 A i).
Proof. exact (eq_refl (term89 A i)). Qed.
Lemma lem7608592 {A : Type'} (i : finite_image A) : (term152 A i) = (term90 A i).
Proof. exact (MK_COMB (@lem7608591 A i) (@lem7608590 A i)). Qed.
Lemma lem7608593 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7608594 {A : Type'} (i : finite_image A) : (term157 A i) = (term158 A i).
Proof. exact (MK_COMB (@lem7608593) (@lem7608592 A i)). Qed.
Lemma lem7608595 {A : Type'} (i : finite_image A) (n : nat) : (term154 A i n) = (term78 A i n).
Proof. exact (eq_refl (term154 A i n)). Qed.
Lemma lem7608596 {A : Type'} (i : finite_image A) : (term89 A i) = (term89 A i).
Proof. exact (eq_refl (term89 A i)). Qed.
Lemma lem7608597 {A : Type'} (i : finite_image A) (n : nat) : (term159 A i n) = (term160 A i n).
Proof. exact (MK_COMB (@lem7608596 A i) (@lem7608595 A i n)). Qed.
Lemma lem7608598 {A : Type'} (i : finite_image A) : (term161 A i) = (term162 A i).
Proof. exact (fun_ext (fun n : nat => @lem7608597 A i n)). Qed.
Lemma lem7608599 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7608600 {A : Type'} (i : finite_image A) : (term153 A i) = (term163 A i).
Proof. exact (MK_COMB (@lem7608599) (@lem7608598 A i)). Qed.
Lemma lem7608601 {A : Type'} (i : finite_image A) : ((term152 A i) = (term153 A i)) = ((term90 A i) = (term163 A i)).
Proof. exact (MK_COMB (@lem7608594 A i) (@lem7608600 A i)). Qed.
Lemma lem7608602 {A : Type'} (i : finite_image A) : (term90 A i) = (term163 A i).
Proof. exact (EQ_MP (@lem7608601 A i) (@lem7608586 A i)). Qed.
Lemma lem7608604 {A : Type'} (P : Prop) (Q : A -> Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7608605 (P : Prop) (Q : nat -> Prop) : (term150 P Q) = (term151 P Q).
Proof. exact (@lem7608604 nat P Q). Qed.
Lemma lem7608606 {A : Type'} (i : finite_image A) (n : nat) : (term164 A i n) = (term165 A i n).
Proof. exact (@lem7608605 (term87 A i) (term76 A i n)). Qed.
Lemma lem7608607 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term166 A i n n') = (term74 A i n' n).
Proof. exact (eq_refl (term166 A i n n')). Qed.
Lemma lem7608608 {A : Type'} (i : finite_image A) (n : nat) : (term167 A i n) = (term76 A i n).
Proof. exact (fun_ext (fun n' : nat => @lem7608607 A i n' n)). Qed.
Lemma lem7608609 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7608610 {A : Type'} (i : finite_image A) (n : nat) : (term168 A i n) = (term78 A i n).
Proof. exact (MK_COMB (@lem7608609) (@lem7608608 A i n)). Qed.
Lemma lem7608611 {A : Type'} (i : finite_image A) : (term89 A i) = (term89 A i).
Proof. exact (eq_refl (term89 A i)). Qed.
Lemma lem7608612 {A : Type'} (i : finite_image A) (n : nat) : (term164 A i n) = (term160 A i n).
Proof. exact (MK_COMB (@lem7608611 A i) (@lem7608610 A i n)). Qed.
Lemma lem7608613 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7608614 {A : Type'} (i : finite_image A) (n : nat) : (term169 A i n) = (term170 A i n).
Proof. exact (MK_COMB (@lem7608613) (@lem7608612 A i n)). Qed.
Lemma lem7608615 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term166 A i n n') = (term74 A i n' n).
Proof. exact (eq_refl (term166 A i n n')). Qed.
Lemma lem7608616 {A : Type'} (i : finite_image A) : (term89 A i) = (term89 A i).
Proof. exact (eq_refl (term89 A i)). Qed.
Lemma lem7608617 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term171 A i n n') = (term172 A i n' n).
Proof. exact (MK_COMB (@lem7608616 A i) (@lem7608615 A i n' n)). Qed.
Lemma lem7608618 {A : Type'} (i : finite_image A) (n : nat) : (term173 A i n) = (term174 A i n).
Proof. exact (fun_ext (fun n' : nat => @lem7608617 A i n' n)). Qed.
Lemma lem7608619 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7608620 {A : Type'} (i : finite_image A) (n : nat) : (term165 A i n) = (term175 A i n).
Proof. exact (MK_COMB (@lem7608619) (@lem7608618 A i n)). Qed.
Lemma lem7608621 {A : Type'} (i : finite_image A) (n : nat) : ((term164 A i n) = (term165 A i n)) = ((term160 A i n) = (term175 A i n)).
Proof. exact (MK_COMB (@lem7608614 A i n) (@lem7608620 A i n)). Qed.
Lemma lem7608622 {A : Type'} (i : finite_image A) (n : nat) : (term160 A i n) = (term175 A i n).
Proof. exact (EQ_MP (@lem7608621 A i n) (@lem7608606 A i n)). Qed.
Lemma lem7608623 {A : Type'} (i : finite_image A) : (term162 A i) = (term176 A i).
Proof. exact (fun_ext (fun n : nat => @lem7608622 A i n)). Qed.
Lemma lem7608624 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7608625 {A : Type'} (i : finite_image A) : (term163 A i) = (term177 A i).
Proof. exact (MK_COMB (@lem7608624) (@lem7608623 A i)). Qed.
Lemma lem7608626 {A : Type'} (i : finite_image A) : (term90 A i) = (term177 A i).
Proof. exact (TRANS (@lem7608602 A i) (@lem7608625 A i)). Qed.
Lemma lem7608627 {A : Type'} : (term97 A) = (term178 A).
Proof. exact (fun_ext (fun i : finite_image A => @lem7608626 A i)). Qed.
Lemma lem7608628 {A : Type'} : (@ex (finite_image A)) = (@ex (finite_image A)).
Proof. exact (eq_refl (@ex (finite_image A))). Qed.
Lemma lem7608629 {A : Type'} : (term98 A) = (term179 A).
Proof. exact (MK_COMB (@lem7608628 A) (@lem7608627 A)). Qed.
Lemma lem7608630 {A : Type'} : (term122 A) = (term179 A).
Proof. exact (TRANS (@lem7608582 A) (@lem7608629 A)). Qed.
Lemma lem7608631 {A : Type'} : (term143 A) = (term179 A).
Proof. exact (TRANS (@lem7608555 A) (@lem7608630 A)). Qed.
Lemma lem7608632 {A : Type'} : (term98 A) = (term179 A).
Proof. exact (TRANS (@lem7608527 A) (@lem7608631 A)). Qed.
Lemma lem7608633 {A : Type'} : (term44 A) = (term179 A).
Proof. exact (TRANS (@lem7608311 A) (@lem7608632 A)). Qed.
Lemma lem7608634 {A : Type'} (h1 : term44 A) : term179 A.
Proof. exact (EQ_MP (@lem7608633 A) (@lem7608257 A h1)). Qed.
Lemma lem7608635 {A : Type'} (a : finite_image A) : ((term57 A a) = a) = ((term57 A a) = a).
Proof. exact (eq_refl ((term57 A a) = a)). Qed.
Lemma lem7608636 {A : Type'} : (term58 A) = (term58 A).
Proof. exact (fun_ext (fun a : finite_image A => @lem7608635 A a)). Qed.
Lemma lem7608637 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7608638 {A : Type'} : (term59 A) = (term59 A).
Proof. exact (MK_COMB (@lem7608637 A) (@lem7608636 A)). Qed.
Lemma lem7608653 {A : Type'} (r : nat) : ((term29 A r) = ((term54 A r) = r)) = (term180 A r).
Proof. exact (@lem17784 (term29 A r) ((term54 A r) = r)). Qed.
Lemma lem7608654 {A : Type'} : (term55 A) = (term181 A).
Proof. exact (fun_ext (fun r : nat => @lem7608653 A r)). Qed.
Lemma lem7608655 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7608656 {A : Type'} : (term56 A) = (term182 A).
Proof. exact (MK_COMB (@lem7608655) (@lem7608654 A)). Qed.
Lemma lem7608657 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7608658 {A : Type'} : (term60 A) = (term60 A).
Proof. exact (MK_COMB (@lem7608657) (@lem7608638 A)). Qed.
Lemma lem7608659 {A : Type'} : (term45 A) = (term183 A).
Proof. exact (MK_COMB (@lem7608658 A) (@lem7608656 A)). Qed.
Lemma lem7608665 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term184 A P Q) = (term185 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7608666 (P : nat -> Prop) (Q : nat -> Prop) : (term186 P Q) = (term187 P Q).
Proof. exact (@lem7608665 nat P Q). Qed.
Lemma lem7608667 {A : Type'} : (term188 A) = (term189 A).
Proof. exact (@lem7608666 (term190 A) (term191 A)). Qed.
Lemma lem7608668 {A : Type'} (r : nat) : (term192 A r) = (term193 A r).
Proof. exact (eq_refl (term192 A r)). Qed.
Lemma lem7608669 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7608670 {A : Type'} (r : nat) : (term194 A r) = (term195 A r).
Proof. exact (MK_COMB (@lem7608669) (@lem7608668 A r)). Qed.
Lemma lem7608671 {A : Type'} (r : nat) : (term196 A r) = (term197 A r).
Proof. exact (eq_refl (term196 A r)). Qed.
Lemma lem7608672 {A : Type'} (r : nat) : (term198 A r) = (term180 A r).
Proof. exact (MK_COMB (@lem7608670 A r) (@lem7608671 A r)). Qed.
Lemma lem7608673 {A : Type'} : (term199 A) = (term181 A).
Proof. exact (fun_ext (fun r : nat => @lem7608672 A r)). Qed.
Lemma lem7608674 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7608675 {A : Type'} : (term188 A) = (term182 A).
Proof. exact (MK_COMB (@lem7608674) (@lem7608673 A)). Qed.
Lemma lem7608676 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7608677 {A : Type'} : (term200 A) = (term201 A).
Proof. exact (MK_COMB (@lem7608676) (@lem7608675 A)). Qed.
Lemma lem7608678 {A : Type'} (r : nat) : (term192 A r) = (term193 A r).
Proof. exact (eq_refl (term192 A r)). Qed.
Lemma lem7608679 {A : Type'} : (term202 A) = (term190 A).
Proof. exact (fun_ext (fun r : nat => @lem7608678 A r)). Qed.
Lemma lem7608680 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7608681 {A : Type'} : (term203 A) = (term204 A).
Proof. exact (MK_COMB (@lem7608680) (@lem7608679 A)). Qed.
Lemma lem7608682 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7608683 {A : Type'} : (term205 A) = (term206 A).
Proof. exact (MK_COMB (@lem7608682) (@lem7608681 A)). Qed.
Lemma lem7608684 {A : Type'} (r : nat) : (term196 A r) = (term197 A r).
Proof. exact (eq_refl (term196 A r)). Qed.
Lemma lem7608685 {A : Type'} : (term207 A) = (term191 A).
Proof. exact (fun_ext (fun r : nat => @lem7608684 A r)). Qed.
Lemma lem7608686 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7608687 {A : Type'} : (term208 A) = (term209 A).
Proof. exact (MK_COMB (@lem7608686) (@lem7608685 A)). Qed.
Lemma lem7608688 {A : Type'} : (term189 A) = (term210 A).
Proof. exact (MK_COMB (@lem7608683 A) (@lem7608687 A)). Qed.
Lemma lem7608689 {A : Type'} : ((term188 A) = (term189 A)) = ((term182 A) = (term210 A)).
Proof. exact (MK_COMB (@lem7608677 A) (@lem7608688 A)). Qed.
Lemma lem7608690 {A : Type'} : (term182 A) = (term210 A).
Proof. exact (EQ_MP (@lem7608689 A) (@lem7608667 A)). Qed.
Lemma lem7608787 {A : Type'} : (term60 A) = (term60 A).
Proof. exact (eq_refl (term60 A)). Qed.
Lemma lem7608790 {A : Type'} : (term183 A) = (term211 A).
Proof. exact (MK_COMB (@lem7608787 A) (@lem7608690 A)). Qed.
Lemma lem7608791 {A : Type'} : (term45 A) = (term211 A).
Proof. exact (TRANS (@lem7608659 A) (@lem7608790 A)). Qed.
Lemma lem7608792 {A : Type'} (h1 : term45 A) : term211 A.
Proof. exact (EQ_MP (@lem7608791 A) (@lem7608258 A h1)). Qed.
Lemma lem7608793 {A : Type'} (i : finite_image A) (h1 : term177 A i) : term177 A i.
Proof. exact (h1). Qed.
Lemma lem7608794 {A : Type'} (i : finite_image A) (n : nat) (h1 : term175 A i n) : term175 A i n.
Proof. exact (h1). Qed.
Lemma lem7608795 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term172 A i n' n) : term172 A i n' n.
Proof. exact (h1). Qed.
Lemma lem7608824 {A : Type'} (r : nat) : (term197 A r) = (term197 A r).
Proof. exact (eq_refl (term197 A r)). Qed.
Lemma lem7608825 {A : Type'} : (term191 A) = (term191 A).
Proof. exact (fun_ext (fun r : nat => @lem7608824 A r)). Qed.
Lemma lem7608826 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7608827 {A : Type'} : (term209 A) = (term209 A).
Proof. exact (MK_COMB (@lem7608826) (@lem7608825 A)). Qed.
Lemma lem7608856 {A : Type'} (r : nat) : (term193 A r) = (term193 A r).
Proof. exact (eq_refl (term193 A r)). Qed.
Lemma lem7608857 {A : Type'} : (term190 A) = (term190 A).
Proof. exact (fun_ext (fun r : nat => @lem7608856 A r)). Qed.
Lemma lem7608858 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7608859 {A : Type'} : (term204 A) = (term204 A).
Proof. exact (MK_COMB (@lem7608858) (@lem7608857 A)). Qed.
Lemma lem7608860 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7608861 {A : Type'} : (term206 A) = (term206 A).
Proof. exact (MK_COMB (@lem7608860) (@lem7608859 A)). Qed.
Lemma lem7608862 {A : Type'} : (term210 A) = (term210 A).
Proof. exact (MK_COMB (@lem7608861 A) (@lem7608827 A)). Qed.
Lemma lem7608871 {A : Type'} (a : finite_image A) : ((term57 A a) = a) = ((term57 A a) = a).
Proof. exact (eq_refl ((term57 A a) = a)). Qed.
Lemma lem7608872 {A : Type'} : (term58 A) = (term58 A).
Proof. exact (fun_ext (fun a : finite_image A => @lem7608871 A a)). Qed.
Lemma lem7608873 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7608874 {A : Type'} : (term59 A) = (term59 A).
Proof. exact (MK_COMB (@lem7608873 A) (@lem7608872 A)). Qed.
Lemma lem7608875 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7608876 {A : Type'} : (term60 A) = (term60 A).
Proof. exact (MK_COMB (@lem7608875) (@lem7608874 A)). Qed.
Lemma lem7608877 {A : Type'} : (term211 A) = (term211 A).
Proof. exact (MK_COMB (@lem7608876 A) (@lem7608862 A)). Qed.
Lemma lem7608878 {A : Type'} (h1 : term45 A) : term211 A.
Proof. exact (EQ_MP (@lem7608877 A) (@lem7608792 A h1)). Qed.
Lemma lem7608941 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term74 A i n' n) = (term74 A i n' n).
Proof. exact (eq_refl (term74 A i n' n)). Qed.
Lemma lem7608970 {A : Type'} (n : nat) (i : finite_image A) : (term62 A n i) = (term62 A n i).
Proof. exact (eq_refl (term62 A n i)). Qed.
Lemma lem7608971 {A : Type'} (i : finite_image A) : (term85 A i) = (term85 A i).
Proof. exact (fun_ext (fun n : nat => @lem7608970 A n i)). Qed.
Lemma lem7608972 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7608973 {A : Type'} (i : finite_image A) : (term87 A i) = (term87 A i).
Proof. exact (MK_COMB (@lem7608972) (@lem7608971 A i)). Qed.
Lemma lem7608974 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7608975 {A : Type'} (i : finite_image A) : (term89 A i) = (term89 A i).
Proof. exact (MK_COMB (@lem7608974) (@lem7608973 A i)). Qed.
Lemma lem7608976 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : (term172 A i n' n) = (term172 A i n' n).
Proof. exact (MK_COMB (@lem7608975 A i) (@lem7608941 A i n' n)). Qed.
Lemma lem7608977 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term172 A i n' n) : term172 A i n' n.
Proof. exact (EQ_MP (@lem7608976 A i n' n) (@lem7608795 A i n' n h1)). Qed.
Lemma lem7608978 {A : Type'} (h1 : term45 A) : term210 A.
Proof. exact (proj2 (@lem7608878 A h1)). Qed.
Lemma lem7608979 {A : Type'} (h1 : term45 A) : term59 A.
Proof. exact (proj1 (@lem7608878 A h1)). Qed.
Lemma lem7608980 {A : Type'} (h1 : term45 A) : term209 A.
Proof. exact (proj2 (@lem7608978 A h1)). Qed.
Lemma lem7608981 {A : Type'} (h1 : term45 A) : term204 A.
Proof. exact (proj1 (@lem7608978 A h1)). Qed.
Lemma lem7608982 {A : Type'} (i : finite_image A) (h1 : term87 A i) : term87 A i.
Proof. exact (h1). Qed.
Lemma lem7608983 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term74 A i n' n) : term74 A i n' n.
Proof. exact (h1). Qed.
Lemma lem7608984 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term74 A i n' n) : term72 A i n' n.
Proof. exact (proj2 (@lem7608983 A i n' n h1)). Qed.
Lemma lem7608985 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term74 A i n' n) : term33 A n i.
Proof. exact (proj1 (@lem7608983 A i n' n h1)). Qed.
Lemma lem7608987 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term74 A i n' n) : term33 A n' i.
Proof. exact (proj1 (@lem7608984 A i n' n h1)). Qed.
Lemma lem7608993 {A : Type'} (a : finite_image A) : ((term57 A a) = a) = ((term57 A a) = a).
Proof. exact (eq_refl ((term57 A a) = a)). Qed.
Lemma lem7608994 {A : Type'} : (term58 A) = (term58 A).
Proof. exact (fun_ext (fun a : finite_image A => @lem7608993 A a)). Qed.
Lemma lem7608995 {A : Type'} : (@all (finite_image A)) = (@all (finite_image A)).
Proof. exact (eq_refl (@all (finite_image A))). Qed.
Lemma lem7608997 {A : Type'} : (term59 A) = (term59 A).
Proof. exact (MK_COMB (@lem7608995 A) (@lem7608994 A)). Qed.
Lemma lem7608998 {A : Type'} (h1 : term45 A) : term59 A.
Proof. exact (EQ_MP (@lem7608997 A) (@lem7608979 A h1)). Qed.
Lemma lem7609006 {A : Type'} (r : nat) : (term193 A r) = (term193 A r).
Proof. exact (eq_refl (term193 A r)). Qed.
Lemma lem7609007 {A : Type'} : (term190 A) = (term190 A).
Proof. exact (fun_ext (fun r : nat => @lem7609006 A r)). Qed.
Lemma lem7609008 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7609010 {A : Type'} : (term204 A) = (term204 A).
Proof. exact (MK_COMB (@lem7609008) (@lem7609007 A)). Qed.
Lemma lem7609011 {A : Type'} (h1 : term45 A) : term204 A.
Proof. exact (EQ_MP (@lem7609010 A) (@lem7608981 A h1)). Qed.
Lemma lem7609032 {A : Type'} (n : nat) (i : finite_image A) : (term62 A n i) = (term62 A n i).
Proof. exact (eq_refl (term62 A n i)). Qed.
Lemma lem7609033 {A : Type'} (i : finite_image A) : (term85 A i) = (term85 A i).
Proof. exact (fun_ext (fun n : nat => @lem7609032 A n i)). Qed.
Lemma lem7609034 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7609036 {A : Type'} (i : finite_image A) : (term87 A i) = (term87 A i).
Proof. exact (MK_COMB (@lem7609034) (@lem7609033 A i)). Qed.
Lemma lem7609037 {A : Type'} (i : finite_image A) (h1 : term87 A i) : term87 A i.
Proof. exact (EQ_MP (@lem7609036 A i) (@lem7608982 A i h1)). Qed.
Lemma lem7609065 {A : Type'} (r : nat) : (term197 A r) = (term197 A r).
Proof. exact (eq_refl (term197 A r)). Qed.
Lemma lem7609066 {A : Type'} : (term191 A) = (term191 A).
Proof. exact (fun_ext (fun r : nat => @lem7609065 A r)). Qed.
Lemma lem7609067 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7609069 {A : Type'} : (term209 A) = (term209 A).
Proof. exact (MK_COMB (@lem7609067) (@lem7609066 A)). Qed.
Lemma lem7609070 {A : Type'} (h1 : term45 A) : term209 A.
Proof. exact (EQ_MP (@lem7609069 A) (@lem7608980 A h1)). Qed.
Lemma lem7609091 {A : Type'} (_97852 : finite_image A) (h1 : term45 A) : term212 A _97852.
Proof. exact (@lem7608998 A h1 _97852). Qed.
Lemma lem7609092 {A : Type'} (_97852 : finite_image A) : (term212 A _97852) = ((term57 A _97852) = _97852).
Proof. exact (eq_refl (term212 A _97852)). Qed.
Lemma lem7609094 {A : Type'} (_97853 : nat) (h1 : term45 A) : term192 A _97853.
Proof. exact (@lem7609011 A h1 _97853). Qed.
Lemma lem7609095 {A : Type'} (_97853 : nat) : (term192 A _97853) = (term193 A _97853).
Proof. exact (eq_refl (term192 A _97853)). Qed.
Lemma lem7609100 {A : Type'} (_97855 : nat) (i : finite_image A) (h1 : term87 A i) : term213 A i _97855.
Proof. exact (@lem7609037 A i h1 _97855). Qed.
Lemma lem7609101 {A : Type'} (_97855 : nat) (i : finite_image A) : (term213 A i _97855) = (term62 A _97855 i).
Proof. exact (eq_refl (term213 A i _97855)). Qed.
Lemma lem7609109 {A : Type'} (_97858 : nat) (h1 : term45 A) : term196 A _97858.
Proof. exact (@lem7609070 A h1 _97858). Qed.
Lemma lem7609110 {A : Type'} (_97858 : nat) : (term196 A _97858) = (term197 A _97858).
Proof. exact (eq_refl (term196 A _97858)). Qed.
Lemma lem7609119 {A : Type'} (_97853 : nat) (h1 : term45 A) : term193 A _97853.
Proof. exact (EQ_MP (@lem7609095 A _97853) (@lem7609094 A _97853 h1)). Qed.
Lemma lem7609131 {A : Type'} (_97855 : nat) (i : finite_image A) (h1 : term87 A i) : term62 A _97855 i.
Proof. exact (EQ_MP (@lem7609101 A _97855 i) (@lem7609100 A _97855 i h1)). Qed.
Lemma lem7609151 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term74 A i n' n) : (@finite_index A n') = i.
Proof. exact (proj2 (@lem7608987 A i n' n h1)). Qed.
Lemma lem7609155 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term74 A i n' n) : (@finite_index A n) = i.
Proof. exact (proj2 (@lem7608985 A i n' n h1)). Qed.
Lemma lem7609156 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term74 A i n' n) : i = (@finite_index A n).
Proof. exact (SYM (@lem7609155 A i n' n h1)). Qed.
Lemma lem7609212 {A : Type'} (_97858 : nat) (h1 : term45 A) : term197 A _97858.
Proof. exact (EQ_MP (@lem7609110 A _97858) (@lem7609109 A _97858 h1)). Qed.
Lemma lem7609226 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term74 A i n' n) : term63 n' n.
Proof. exact (proj2 (@lem7608984 A i n' n h1)). Qed.
Lemma lem7609241 {A : Type'} (n' : nat) : (term214 A n') = (term214 A n').
Proof. exact (eq_refl (term214 A n')). Qed.
Lemma lem7609242 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term74 A i n' n) : (term215 A n' i) = (term216 A n' n).
Proof. exact (MK_COMB (@lem7609241 A n') (@lem7609156 A i n' n h1)). Qed.
Lemma lem7609243 {A : Type'} (n' : nat) (n : nat) : (term216 A n' n) = ((@finite_index A n') = (@finite_index A n)).
Proof. exact (eq_refl (term216 A n' n)). Qed.
Lemma lem7609244 {A : Type'} (n' : nat) (i : finite_image A) : (term217 A n' i) = (term217 A n' i).
Proof. exact (eq_refl (term217 A n' i)). Qed.
Lemma lem7609245 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : ((term215 A n' i) = (term216 A n' n)) = ((term215 A n' i) = ((@finite_index A n') = (@finite_index A n))).
Proof. exact (MK_COMB (@lem7609244 A n' i) (@lem7609243 A n' n)). Qed.
Lemma lem7609246 {A : Type'} (n' : nat) (i : finite_image A) : (term215 A n' i) = ((@finite_index A n') = i).
Proof. exact (eq_refl (term215 A n' i)). Qed.
Lemma lem7609247 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7609248 {A : Type'} (n' : nat) (i : finite_image A) : (term217 A n' i) = (term218 A n' i).
Proof. exact (MK_COMB (@lem7609247) (@lem7609246 A n' i)). Qed.
Lemma lem7609249 {A : Type'} (n' : nat) (n : nat) : ((@finite_index A n') = (@finite_index A n)) = ((@finite_index A n') = (@finite_index A n)).
Proof. exact (eq_refl ((@finite_index A n') = (@finite_index A n))). Qed.
Lemma lem7609250 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : ((term215 A n' i) = ((@finite_index A n') = (@finite_index A n))) = (((@finite_index A n') = i) = ((@finite_index A n') = (@finite_index A n))).
Proof. exact (MK_COMB (@lem7609248 A n' i) (@lem7609249 A n' n)). Qed.
Lemma lem7609251 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) : ((term215 A n' i) = (term216 A n' n)) = (((@finite_index A n') = i) = ((@finite_index A n') = (@finite_index A n))).
Proof. exact (TRANS (@lem7609245 A i n' n) (@lem7609250 A i n' n)). Qed.
Lemma lem7609252 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term74 A i n' n) : ((@finite_index A n') = i) = ((@finite_index A n') = (@finite_index A n)).
Proof. exact (EQ_MP (@lem7609251 A i n' n) (@lem7609242 A i n' n h1)). Qed.
Lemma lem7609326 {A : Type'} : (@dest_finite_image A) = (@dest_finite_image A).
Proof. exact (eq_refl (@dest_finite_image A)). Qed.
Lemma lem7609327 {A : Type'} (_97889 : finite_image A) (_97890 : finite_image A) (h1 : _97889 = _97890) : _97889 = _97890.
Proof. exact (h1). Qed.
Lemma lem7609328 {A : Type'} (_97889 : finite_image A) (_97890 : finite_image A) (h1 : _97889 = _97890) : (@dest_finite_image A _97889) = (@dest_finite_image A _97890).
Proof. exact (MK_COMB (@lem7609326 A) (@lem7609327 A _97889 _97890 h1)). Qed.
Lemma lem7609329 {A : Type'} (_97889 : finite_image A) (_97890 : finite_image A) : term219 A _97889 _97890.
Proof. exact (fun h0 : _97889 = _97890 => @lem7609328 A _97889 _97890 h0). Qed.
Lemma lem7609331 (a : Prop) (b : Prop) : (a -> b) = (term220 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7609332 {A : Type'} (_97889 : finite_image A) (_97890 : finite_image A) : (term219 A _97889 _97890) = (term221 A _97889 _97890).
Proof. exact (@lem7609331 (_97889 = _97890) ((@dest_finite_image A _97889) = (@dest_finite_image A _97890))). Qed.
Lemma lem7609333 {A : Type'} (_97889 : finite_image A) (_97890 : finite_image A) : term221 A _97889 _97890.
Proof. exact (EQ_MP (@lem7609332 A _97889 _97890) (@lem7609329 A _97889 _97890)). Qed.
Lemma lem7609351 {A : Type'} (_97852 : finite_image A) (h1 : term45 A) : (term57 A _97852) = _97852.
Proof. exact (EQ_MP (@lem7609092 A _97852) (@lem7609091 A _97852 h1)). Qed.
Lemma lem7609352 {A : Type'} (_97852 : finite_image A) (h1 : term45 A) : (term57 A _97852) = _97852.
Proof. exact (@lem7609351 A _97852 h1). Qed.
Lemma lem7609353 {A : Type'} (i : finite_image A) (h1 : term45 A) : (term57 A i) = i.
Proof. exact (@lem7609352 A i h1). Qed.
Lemma lem7609354 {A : Type'} (i : finite_image A) (h1 : term45 A) : term222 A i.
Proof. exact (fun h0 : term223 A i => @lem7609353 A i h1). Qed.
Lemma lem7609356 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7609357 {A : Type'} (i : finite_image A) : (term222 A i) = ((term57 A i) = i).
Proof. exact (@lem7609356 ((term57 A i) = i)). Qed.
Lemma lem7609358 {A : Type'} (i : finite_image A) (h1 : term45 A) : (term57 A i) = i.
Proof. exact (EQ_MP (@lem7609357 A i) (@lem7609354 A i h1)). Qed.
Lemma lem7609364 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7609365 {A : Type'} (_97889 : finite_image A) (_97890 : finite_image A) : (term221 A _97889 _97890) = (term225 A _97889 _97890).
Proof. exact (@lem7609364 ((@dest_finite_image A _97889) = (@dest_finite_image A _97890)) (term226 A _97889 _97890)). Qed.
Lemma lem7609375 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7609376 {A : Type'} (_97889 : finite_image A) (_97890 : finite_image A) : (term227 A _97889 _97890) = (term228 A _97889 _97890).
Proof. exact (MK_COMB (@lem7609375) (@lem7609365 A _97889 _97890)). Qed.
Lemma lem7609386 {A : Type'} (_97889 : finite_image A) (_97890 : finite_image A) : (term225 A _97889 _97890) = (term225 A _97889 _97890).
Proof. exact (eq_refl (term225 A _97889 _97890)). Qed.
Lemma lem7609387 {A : Type'} (_97889 : finite_image A) (_97890 : finite_image A) : ((term221 A _97889 _97890) = (term225 A _97889 _97890)) = ((term225 A _97889 _97890) = (term225 A _97889 _97890)).
Proof. exact (MK_COMB (@lem7609376 A _97889 _97890) (@lem7609386 A _97889 _97890)). Qed.
Lemma lem7609389 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7609390 (x : Prop) : (x = x) = True.
Proof. exact (@lem7609389 Prop x). Qed.
Lemma lem7609391 {A : Type'} (_97889 : finite_image A) (_97890 : finite_image A) : ((term225 A _97889 _97890) = (term225 A _97889 _97890)) = True.
Proof. exact (@lem7609390 (term225 A _97889 _97890)). Qed.
Lemma lem7609392 {A : Type'} (_97889 : finite_image A) (_97890 : finite_image A) : ((term221 A _97889 _97890) = (term225 A _97889 _97890)) = True.
Proof. exact (TRANS (@lem7609387 A _97889 _97890) (@lem7609391 A _97889 _97890)). Qed.
Lemma lem7609393 {A : Type'} (_97889 : finite_image A) (_97890 : finite_image A) : True = ((term221 A _97889 _97890) = (term225 A _97889 _97890)).
Proof. exact (SYM (@lem7609392 A _97889 _97890)). Qed.
Lemma lem7609394 {A : Type'} (_97889 : finite_image A) (_97890 : finite_image A) : (term221 A _97889 _97890) = (term225 A _97889 _97890).
Proof. exact (EQ_MP (@lem7609393 A _97889 _97890) (@lem0)). Qed.
Lemma lem7609395 {A : Type'} (_97889 : finite_image A) (_97890 : finite_image A) : term225 A _97889 _97890.
Proof. exact (EQ_MP (@lem7609394 A _97889 _97890) (@lem7609333 A _97889 _97890)). Qed.
Lemma lem7609397 (b : Prop) (a : Prop) : (a \/ b) = (term229 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7609398 {A : Type'} (_97889 : finite_image A) (_97890 : finite_image A) : (term225 A _97889 _97890) = (term230 A _97889 _97890).
Proof. exact (@lem7609397 (term226 A _97889 _97890) ((@dest_finite_image A _97889) = (@dest_finite_image A _97890))). Qed.
Lemma lem7609400 (a : Prop) : (term231 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7609401 {A : Type'} (_97889 : finite_image A) (_97890 : finite_image A) : (term232 A _97889 _97890) = (_97889 = _97890).
Proof. exact (@lem7609400 (_97889 = _97890)). Qed.
Lemma lem7609402 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7609403 {A : Type'} (_97889 : finite_image A) (_97890 : finite_image A) : (term233 A _97889 _97890) = (term234 A _97889 _97890).
Proof. exact (MK_COMB (@lem7609402) (@lem7609401 A _97889 _97890)). Qed.
Lemma lem7609404 {A : Type'} (_97889 : finite_image A) (_97890 : finite_image A) : ((@dest_finite_image A _97889) = (@dest_finite_image A _97890)) = ((@dest_finite_image A _97889) = (@dest_finite_image A _97890)).
Proof. exact (eq_refl ((@dest_finite_image A _97889) = (@dest_finite_image A _97890))). Qed.
Lemma lem7609405 {A : Type'} (_97889 : finite_image A) (_97890 : finite_image A) : (term230 A _97889 _97890) = (term219 A _97889 _97890).
Proof. exact (MK_COMB (@lem7609403 A _97889 _97890) (@lem7609404 A _97889 _97890)). Qed.
Lemma lem7609406 {A : Type'} (_97889 : finite_image A) (_97890 : finite_image A) : (term225 A _97889 _97890) = (term219 A _97889 _97890).
Proof. exact (TRANS (@lem7609398 A _97889 _97890) (@lem7609405 A _97889 _97890)). Qed.
Lemma lem7609409 {A : Type'} (_97889 : finite_image A) (_97890 : finite_image A) : term219 A _97889 _97890.
Proof. exact (EQ_MP (@lem7609406 A _97889 _97890) (@lem7609395 A _97889 _97890)). Qed.
Lemma lem7609410 {A : Type'} (_97889 : finite_image A) (_97890 : finite_image A) : term219 A _97889 _97890.
Proof. exact (@lem7609409 A _97889 _97890). Qed.
Lemma lem7609411 {A : Type'} (i : finite_image A) : term235 A i.
Proof. exact (@lem7609410 A (term57 A i) i). Qed.
Lemma lem7609414 {A : Type'} (i : finite_image A) (h1 : term45 A) : (term236 A i) = (@dest_finite_image A i).
Proof. exact (@lem7609411 A i (@lem7609358 A i h1)). Qed.
Lemma lem7609415 {A : Type'} (i : finite_image A) (h1 : term45 A) : (term236 A i) = (@dest_finite_image A i).
Proof. exact (@lem7609414 A i h1). Qed.
Lemma lem7609416 {A : Type'} (i : finite_image A) (h1 : term45 A) : term237 A i.
Proof. exact (fun h0 : term238 A i => @lem7609415 A i h1). Qed.
Lemma lem7609418 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7609419 {A : Type'} (i : finite_image A) : (term237 A i) = ((term236 A i) = (@dest_finite_image A i)).
Proof. exact (@lem7609418 ((term236 A i) = (@dest_finite_image A i))). Qed.
Lemma lem7609420 {A : Type'} (i : finite_image A) (h1 : term45 A) : (term236 A i) = (@dest_finite_image A i).
Proof. exact (EQ_MP (@lem7609419 A i) (@lem7609416 A i h1)). Qed.
Lemma lem7609422 (b : Prop) (a : Prop) : (a \/ b) = (term229 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7609423 {A : Type'} (_97853 : nat) : (term193 A _97853) = (term239 A _97853).
Proof. exact (@lem7609422 (term240 A _97853) (term29 A _97853)). Qed.
Lemma lem7609425 (a : Prop) : (term231 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7609426 {A : Type'} (_97853 : nat) : (term241 A _97853) = ((term54 A _97853) = _97853).
Proof. exact (@lem7609425 ((term54 A _97853) = _97853)). Qed.
Lemma lem7609427 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7609428 {A : Type'} (_97853 : nat) : (term242 A _97853) = (term243 A _97853).
Proof. exact (MK_COMB (@lem7609427) (@lem7609426 A _97853)). Qed.
Lemma lem7609429 {A : Type'} (_97853 : nat) : (term29 A _97853) = (term29 A _97853).
Proof. exact (eq_refl (term29 A _97853)). Qed.
Lemma lem7609430 {A : Type'} (_97853 : nat) : (term239 A _97853) = (term244 A _97853).
Proof. exact (MK_COMB (@lem7609428 A _97853) (@lem7609429 A _97853)). Qed.
Lemma lem7609431 {A : Type'} (_97853 : nat) : (term193 A _97853) = (term244 A _97853).
Proof. exact (TRANS (@lem7609423 A _97853) (@lem7609430 A _97853)). Qed.
Lemma lem7609434 {A : Type'} (_97853 : nat) (h1 : term45 A) : term244 A _97853.
Proof. exact (EQ_MP (@lem7609431 A _97853) (@lem7609119 A _97853 h1)). Qed.
Lemma lem7609435 {A : Type'} (i : finite_image A) (h1 : term45 A) : term245 A i.
Proof. exact (@lem7609434 A (@dest_finite_image A i) h1). Qed.
Lemma lem7609438 {A : Type'} (i : finite_image A) (h1 : term45 A) : term246 A i.
Proof. exact (@lem7609435 A i h1 (@lem7609420 A i h1)). Qed.
Lemma lem7609439 {A : Type'} (i : finite_image A) (h1 : term45 A) : term246 A i.
Proof. exact (@lem7609438 A i h1). Qed.
Lemma lem7609440 {A : Type'} (i : finite_image A) (h1 : term45 A) : term247 A i.
Proof. exact (fun h0 : term248 A i => @lem7609439 A i h1). Qed.
Lemma lem7609442 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7609443 {A : Type'} (i : finite_image A) : (term247 A i) = (term246 A i).
Proof. exact (@lem7609442 (term246 A i)). Qed.
Lemma lem7609444 {A : Type'} (i : finite_image A) (h1 : term45 A) : term246 A i.
Proof. exact (EQ_MP (@lem7609443 A i) (@lem7609440 A i h1)). Qed.
Lemma lem7609446 {A : Type'} (_97852 : finite_image A) (h1 : term45 A) : (term57 A _97852) = _97852.
Proof. exact (EQ_MP (@lem7609092 A _97852) (@lem7609091 A _97852 h1)). Qed.
Lemma lem7609447 {A : Type'} (_97852 : finite_image A) (h1 : term45 A) : (term57 A _97852) = _97852.
Proof. exact (@lem7609446 A _97852 h1). Qed.
Lemma lem7609448 {A : Type'} (i : finite_image A) (h1 : term45 A) : (term57 A i) = i.
Proof. exact (@lem7609447 A i h1). Qed.
Lemma lem7609449 {A : Type'} (i : finite_image A) (h1 : term45 A) : term222 A i.
Proof. exact (fun h0 : term223 A i => @lem7609448 A i h1). Qed.
Lemma lem7609451 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7609452 {A : Type'} (i : finite_image A) : (term222 A i) = ((term57 A i) = i).
Proof. exact (@lem7609451 ((term57 A i) = i)). Qed.
Lemma lem7609453 {A : Type'} (i : finite_image A) (h1 : term45 A) : (term57 A i) = i.
Proof. exact (EQ_MP (@lem7609452 A i) (@lem7609449 A i h1)). Qed.
Lemma lem7609455 (a : Prop) (b : Prop) : (term249 a b) = (term250 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem7609456 {A : Type'} (_97855 : nat) (i : finite_image A) : (term62 A _97855 i) = (term61 A _97855 i).
Proof. exact (@lem7609455 (term29 A _97855) ((@finite_index A _97855) = i)). Qed.
Lemma lem7609458 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7609459 {A : Type'} (_97855 : nat) (i : finite_image A) : (term61 A _97855 i) = (term251 A _97855 i).
Proof. exact (@lem7609458 (term33 A _97855 i)). Qed.
Lemma lem7609460 {A : Type'} (_97855 : nat) (i : finite_image A) : (term62 A _97855 i) = (term251 A _97855 i).
Proof. exact (TRANS (@lem7609456 A _97855 i) (@lem7609459 A _97855 i)). Qed.
Lemma lem7609462 {A : Type'} (i : finite_image A) (h1 : term45 A) : term252 A i.
Proof. exact (conj (@lem7609444 A i h1) (@lem7609453 A i h1)). Qed.
Lemma lem7609464 {A : Type'} (_97855 : nat) (i : finite_image A) (h1 : term87 A i) : term251 A _97855 i.
Proof. exact (EQ_MP (@lem7609460 A _97855 i) (@lem7609131 A _97855 i h1)). Qed.
Lemma lem7609465 {A : Type'} (i : finite_image A) (h1 : term87 A i) : term253 A i.
Proof. exact (@lem7609464 A (@dest_finite_image A i) i h1). Qed.
Lemma lem7609468 {A : Type'} (i : finite_image A) (h1 : term87 A i) (h2 : term45 A) : False.
Proof. exact (@lem7609465 A i h1 (@lem7609462 A i h2)). Qed.
Lemma lem7609469 {A : Type'} (i : finite_image A) (h1 : term87 A i) (h2 : term45 A) : term254.
Proof. exact (fun h0 : ~ False => @lem7609468 A i h1 h2). Qed.
Lemma lem7609471 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7609472 : term254 = False.
Proof. exact (@lem7609471 False). Qed.
Lemma lem7609473 {A : Type'} (i : finite_image A) (h1 : term87 A i) (h2 : term45 A) : False.
Proof. exact (EQ_MP (@lem7609472) (@lem7609469 A i h1 h2)). Qed.
Lemma lem7609532 {A : Type'} : (@dest_finite_image A) = (@dest_finite_image A).
Proof. exact (eq_refl (@dest_finite_image A)). Qed.
Lemma lem7609533 {A : Type'} (_97907 : finite_image A) (_97908 : finite_image A) (h1 : _97907 = _97908) : _97907 = _97908.
Proof. exact (h1). Qed.
Lemma lem7609534 {A : Type'} (_97907 : finite_image A) (_97908 : finite_image A) (h1 : _97907 = _97908) : (@dest_finite_image A _97907) = (@dest_finite_image A _97908).
Proof. exact (MK_COMB (@lem7609532 A) (@lem7609533 A _97907 _97908 h1)). Qed.
Lemma lem7609535 {A : Type'} (_97907 : finite_image A) (_97908 : finite_image A) : term219 A _97907 _97908.
Proof. exact (fun h0 : _97907 = _97908 => @lem7609534 A _97907 _97908 h0). Qed.
Lemma lem7609537 (a : Prop) (b : Prop) : (a -> b) = (term220 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7609538 {A : Type'} (_97907 : finite_image A) (_97908 : finite_image A) : (term219 A _97907 _97908) = (term221 A _97907 _97908).
Proof. exact (@lem7609537 (_97907 = _97908) ((@dest_finite_image A _97907) = (@dest_finite_image A _97908))). Qed.
Lemma lem7609539 {A : Type'} (_97907 : finite_image A) (_97908 : finite_image A) : term221 A _97907 _97908.
Proof. exact (EQ_MP (@lem7609538 A _97907 _97908) (@lem7609535 A _97907 _97908)). Qed.
Lemma lem7609551 (x : nat) (y : nat) (z : nat) : term255 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem7609557 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term74 A i n' n) : (@finite_index A n') = (@finite_index A n).
Proof. exact (EQ_MP (@lem7609252 A i n' n h1) (@lem7609151 A i n' n h1)). Qed.
Lemma lem7609558 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term74 A i n' n) : term256 A n' n.
Proof. exact (fun h0 : term257 A n' n => @lem7609557 A i n' n h1). Qed.
Lemma lem7609560 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7609561 {A : Type'} (n' : nat) (n : nat) : (term256 A n' n) = ((@finite_index A n') = (@finite_index A n)).
Proof. exact (@lem7609560 ((@finite_index A n') = (@finite_index A n))). Qed.
Lemma lem7609562 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term74 A i n' n) : (@finite_index A n') = (@finite_index A n).
Proof. exact (EQ_MP (@lem7609561 A n' n) (@lem7609558 A i n' n h1)). Qed.
Lemma lem7609568 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7609569 {A : Type'} (_97907 : finite_image A) (_97908 : finite_image A) : (term221 A _97907 _97908) = (term225 A _97907 _97908).
Proof. exact (@lem7609568 ((@dest_finite_image A _97907) = (@dest_finite_image A _97908)) (term226 A _97907 _97908)). Qed.
Lemma lem7609579 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7609580 {A : Type'} (_97907 : finite_image A) (_97908 : finite_image A) : (term227 A _97907 _97908) = (term228 A _97907 _97908).
Proof. exact (MK_COMB (@lem7609579) (@lem7609569 A _97907 _97908)). Qed.
Lemma lem7609590 {A : Type'} (_97907 : finite_image A) (_97908 : finite_image A) : (term225 A _97907 _97908) = (term225 A _97907 _97908).
Proof. exact (eq_refl (term225 A _97907 _97908)). Qed.
Lemma lem7609591 {A : Type'} (_97907 : finite_image A) (_97908 : finite_image A) : ((term221 A _97907 _97908) = (term225 A _97907 _97908)) = ((term225 A _97907 _97908) = (term225 A _97907 _97908)).
Proof. exact (MK_COMB (@lem7609580 A _97907 _97908) (@lem7609590 A _97907 _97908)). Qed.
Lemma lem7609593 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7609594 (x : Prop) : (x = x) = True.
Proof. exact (@lem7609593 Prop x). Qed.
Lemma lem7609595 {A : Type'} (_97907 : finite_image A) (_97908 : finite_image A) : ((term225 A _97907 _97908) = (term225 A _97907 _97908)) = True.
Proof. exact (@lem7609594 (term225 A _97907 _97908)). Qed.
Lemma lem7609596 {A : Type'} (_97907 : finite_image A) (_97908 : finite_image A) : ((term221 A _97907 _97908) = (term225 A _97907 _97908)) = True.
Proof. exact (TRANS (@lem7609591 A _97907 _97908) (@lem7609595 A _97907 _97908)). Qed.
Lemma lem7609597 {A : Type'} (_97907 : finite_image A) (_97908 : finite_image A) : True = ((term221 A _97907 _97908) = (term225 A _97907 _97908)).
Proof. exact (SYM (@lem7609596 A _97907 _97908)). Qed.
Lemma lem7609598 {A : Type'} (_97907 : finite_image A) (_97908 : finite_image A) : (term221 A _97907 _97908) = (term225 A _97907 _97908).
Proof. exact (EQ_MP (@lem7609597 A _97907 _97908) (@lem0)). Qed.
Lemma lem7609599 {A : Type'} (_97907 : finite_image A) (_97908 : finite_image A) : term225 A _97907 _97908.
Proof. exact (EQ_MP (@lem7609598 A _97907 _97908) (@lem7609539 A _97907 _97908)). Qed.
Lemma lem7609601 (b : Prop) (a : Prop) : (a \/ b) = (term229 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7609602 {A : Type'} (_97907 : finite_image A) (_97908 : finite_image A) : (term225 A _97907 _97908) = (term230 A _97907 _97908).
Proof. exact (@lem7609601 (term226 A _97907 _97908) ((@dest_finite_image A _97907) = (@dest_finite_image A _97908))). Qed.
Lemma lem7609604 (a : Prop) : (term231 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7609605 {A : Type'} (_97907 : finite_image A) (_97908 : finite_image A) : (term232 A _97907 _97908) = (_97907 = _97908).
Proof. exact (@lem7609604 (_97907 = _97908)). Qed.
Lemma lem7609606 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7609607 {A : Type'} (_97907 : finite_image A) (_97908 : finite_image A) : (term233 A _97907 _97908) = (term234 A _97907 _97908).
Proof. exact (MK_COMB (@lem7609606) (@lem7609605 A _97907 _97908)). Qed.
Lemma lem7609608 {A : Type'} (_97907 : finite_image A) (_97908 : finite_image A) : ((@dest_finite_image A _97907) = (@dest_finite_image A _97908)) = ((@dest_finite_image A _97907) = (@dest_finite_image A _97908)).
Proof. exact (eq_refl ((@dest_finite_image A _97907) = (@dest_finite_image A _97908))). Qed.
Lemma lem7609609 {A : Type'} (_97907 : finite_image A) (_97908 : finite_image A) : (term230 A _97907 _97908) = (term219 A _97907 _97908).
Proof. exact (MK_COMB (@lem7609607 A _97907 _97908) (@lem7609608 A _97907 _97908)). Qed.
Lemma lem7609610 {A : Type'} (_97907 : finite_image A) (_97908 : finite_image A) : (term225 A _97907 _97908) = (term219 A _97907 _97908).
Proof. exact (TRANS (@lem7609602 A _97907 _97908) (@lem7609609 A _97907 _97908)). Qed.
Lemma lem7609613 {A : Type'} (_97907 : finite_image A) (_97908 : finite_image A) : term219 A _97907 _97908.
Proof. exact (EQ_MP (@lem7609610 A _97907 _97908) (@lem7609599 A _97907 _97908)). Qed.
Lemma lem7609614 {A : Type'} (_97907 : finite_image A) (_97908 : finite_image A) : term219 A _97907 _97908.
Proof. exact (@lem7609613 A _97907 _97908). Qed.
Lemma lem7609615 {A : Type'} (n' : nat) (n : nat) : term258 A n' n.
Proof. exact (@lem7609614 A (@finite_index A n') (@finite_index A n)). Qed.
Lemma lem7609618 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term74 A i n' n) : (term54 A n') = (term54 A n).
Proof. exact (@lem7609615 A n' n (@lem7609562 A i n' n h1)). Qed.
Lemma lem7609619 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term74 A i n' n) : term259 A n' n.
Proof. exact (fun h0 : term260 A n' n => @lem7609618 A i n' n h1). Qed.
Lemma lem7609621 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7609622 {A : Type'} (n' : nat) (n : nat) : (term259 A n' n) = ((term54 A n') = (term54 A n)).
Proof. exact (@lem7609621 ((term54 A n') = (term54 A n))). Qed.
Lemma lem7609623 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term74 A i n' n) : (term54 A n') = (term54 A n).
Proof. exact (EQ_MP (@lem7609622 A n' n) (@lem7609619 A i n' n h1)). Qed.
Lemma lem7609625 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term74 A i n' n) : term29 A n'.
Proof. exact (proj1 (@lem7608987 A i n' n h1)). Qed.
Lemma lem7609626 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term74 A i n' n) : term261 A n'.
Proof. exact (fun h0 : term262 A n' => @lem7609625 A i n' n h1). Qed.
Lemma lem7609628 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7609629 {A : Type'} (n' : nat) : (term261 A n') = (term29 A n').
Proof. exact (@lem7609628 (term29 A n')). Qed.
Lemma lem7609630 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term74 A i n' n) : term29 A n'.
Proof. exact (EQ_MP (@lem7609629 A n') (@lem7609626 A i n' n h1)). Qed.
Lemma lem7609636 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7609637 {A : Type'} (_97858 : nat) : (term197 A _97858) = (term263 A _97858).
Proof. exact (@lem7609636 ((term54 A _97858) = _97858) (term262 A _97858)). Qed.
Lemma lem7609645 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7609646 {A : Type'} (_97858 : nat) : (term264 A _97858) = (term265 A _97858).
Proof. exact (MK_COMB (@lem7609645) (@lem7609637 A _97858)). Qed.
Lemma lem7609654 {A : Type'} (_97858 : nat) : (term263 A _97858) = (term263 A _97858).
Proof. exact (eq_refl (term263 A _97858)). Qed.
Lemma lem7609655 {A : Type'} (_97858 : nat) : ((term197 A _97858) = (term263 A _97858)) = ((term263 A _97858) = (term263 A _97858)).
Proof. exact (MK_COMB (@lem7609646 A _97858) (@lem7609654 A _97858)). Qed.
Lemma lem7609657 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7609658 (x : Prop) : (x = x) = True.
Proof. exact (@lem7609657 Prop x). Qed.
Lemma lem7609659 {A : Type'} (_97858 : nat) : ((term263 A _97858) = (term263 A _97858)) = True.
Proof. exact (@lem7609658 (term263 A _97858)). Qed.
Lemma lem7609660 {A : Type'} (_97858 : nat) : ((term197 A _97858) = (term263 A _97858)) = True.
Proof. exact (TRANS (@lem7609655 A _97858) (@lem7609659 A _97858)). Qed.
Lemma lem7609661 {A : Type'} (_97858 : nat) : True = ((term197 A _97858) = (term263 A _97858)).
Proof. exact (SYM (@lem7609660 A _97858)). Qed.
Lemma lem7609662 {A : Type'} (_97858 : nat) : (term197 A _97858) = (term263 A _97858).
Proof. exact (EQ_MP (@lem7609661 A _97858) (@lem0)). Qed.
Lemma lem7609663 {A : Type'} (_97858 : nat) (h1 : term45 A) : term263 A _97858.
Proof. exact (EQ_MP (@lem7609662 A _97858) (@lem7609212 A _97858 h1)). Qed.
Lemma lem7609665 (b : Prop) (a : Prop) : (a \/ b) = (term229 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7609666 {A : Type'} (_97858 : nat) : (term263 A _97858) = (term266 A _97858).
Proof. exact (@lem7609665 (term262 A _97858) ((term54 A _97858) = _97858)). Qed.
Lemma lem7609668 (a : Prop) : (term231 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7609669 {A : Type'} (_97858 : nat) : (term267 A _97858) = (term29 A _97858).
Proof. exact (@lem7609668 (term29 A _97858)). Qed.
Lemma lem7609670 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7609671 {A : Type'} (_97858 : nat) : (term268 A _97858) = (term269 A _97858).
Proof. exact (MK_COMB (@lem7609670) (@lem7609669 A _97858)). Qed.
Lemma lem7609672 {A : Type'} (_97858 : nat) : ((term54 A _97858) = _97858) = ((term54 A _97858) = _97858).
Proof. exact (eq_refl ((term54 A _97858) = _97858)). Qed.
Lemma lem7609673 {A : Type'} (_97858 : nat) : (term266 A _97858) = (term270 A _97858).
Proof. exact (MK_COMB (@lem7609671 A _97858) (@lem7609672 A _97858)). Qed.
Lemma lem7609674 {A : Type'} (_97858 : nat) : (term263 A _97858) = (term270 A _97858).
Proof. exact (TRANS (@lem7609666 A _97858) (@lem7609673 A _97858)). Qed.
Lemma lem7609677 {A : Type'} (_97858 : nat) (h1 : term45 A) : term270 A _97858.
Proof. exact (EQ_MP (@lem7609674 A _97858) (@lem7609663 A _97858 h1)). Qed.
Lemma lem7609678 {A : Type'} (n' : nat) (h1 : term45 A) : term270 A n'.
Proof. exact (@lem7609677 A n' h1). Qed.
Lemma lem7609681 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term45 A) (h2 : term74 A i n' n) : (term54 A n') = n'.
Proof. exact (@lem7609678 A n' h1 (@lem7609630 A i n' n h2)). Qed.
Lemma lem7609682 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term45 A) (h2 : term74 A i n' n) : term271 A n'.
Proof. exact (fun h0 : term240 A n' => @lem7609681 A i n' n h1 h2). Qed.
Lemma lem7609684 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7609685 {A : Type'} (n' : nat) : (term271 A n') = ((term54 A n') = n').
Proof. exact (@lem7609684 ((term54 A n') = n')). Qed.
Lemma lem7609686 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term45 A) (h2 : term74 A i n' n) : (term54 A n') = n'.
Proof. exact (EQ_MP (@lem7609685 A n') (@lem7609682 A i n' n h1 h2)). Qed.
Lemma lem7609704 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7609705 (y : nat) (x : nat) (z : nat) : (term272 x y z) = (term273 y x z).
Proof. exact (@lem7609704 (y = z) (term63 x z)). Qed.
Lemma lem7609715 (x : nat) (y : nat) : (term274 x y) = (term274 x y).
Proof. exact (eq_refl (term274 x y)). Qed.
Lemma lem7609716 (y : nat) (x : nat) (z : nat) : (term255 x y z) = (term275 y x z).
Proof. exact (MK_COMB (@lem7609715 x y) (@lem7609705 y x z)). Qed.
Lemma lem7609720 (q : Prop) (p : Prop) (r : Prop) : (term276 p q r) = (term276 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7609721 (y : nat) (x : nat) (z : nat) : (term275 y x z) = (term277 y x z).
Proof. exact (@lem7609720 (y = z) (term63 x y) (term63 x z)). Qed.
Lemma lem7609743 (y : nat) (x : nat) (z : nat) : (term255 x y z) = (term277 y x z).
Proof. exact (TRANS (@lem7609716 y x z) (@lem7609721 y x z)). Qed.
Lemma lem7609744 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7609745 (y : nat) (x : nat) (z : nat) : (term278 x y z) = (term279 y x z).
Proof. exact (MK_COMB (@lem7609744) (@lem7609743 y x z)). Qed.
Lemma lem7609767 (y : nat) (x : nat) (z : nat) : (term277 y x z) = (term277 y x z).
Proof. exact (eq_refl (term277 y x z)). Qed.
Lemma lem7609768 (y : nat) (x : nat) (z : nat) : ((term255 x y z) = (term277 y x z)) = ((term277 y x z) = (term277 y x z)).
Proof. exact (MK_COMB (@lem7609745 y x z) (@lem7609767 y x z)). Qed.
Lemma lem7609770 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7609771 (x : Prop) : (x = x) = True.
Proof. exact (@lem7609770 Prop x). Qed.
Lemma lem7609772 (y : nat) (x : nat) (z : nat) : ((term277 y x z) = (term277 y x z)) = True.
Proof. exact (@lem7609771 (term277 y x z)). Qed.
Lemma lem7609773 (y : nat) (x : nat) (z : nat) : ((term255 x y z) = (term277 y x z)) = True.
Proof. exact (TRANS (@lem7609768 y x z) (@lem7609772 y x z)). Qed.
Lemma lem7609774 (y : nat) (x : nat) (z : nat) : True = ((term255 x y z) = (term277 y x z)).
Proof. exact (SYM (@lem7609773 y x z)). Qed.
Lemma lem7609775 (y : nat) (x : nat) (z : nat) : (term255 x y z) = (term277 y x z).
Proof. exact (EQ_MP (@lem7609774 y x z) (@lem0)). Qed.
Lemma lem7609776 (y : nat) (x : nat) (z : nat) : term277 y x z.
Proof. exact (EQ_MP (@lem7609775 y x z) (@lem7609551 x y z)). Qed.
Lemma lem7609778 (b : Prop) (a : Prop) : (a \/ b) = (term229 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7609779 (x : nat) (y : nat) (z : nat) : (term277 y x z) = (term280 x y z).
Proof. exact (@lem7609778 (term281 y x z) (y = z)). Qed.
Lemma lem7609781 (a : Prop) (b : Prop) : (term282 a b) = (term283 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7609782 (y : nat) (x : nat) (z : nat) : (term284 y x z) = (term285 y x z).
Proof. exact (@lem7609781 (term63 x y) (term63 x z)). Qed.
Lemma lem7609784 (a : Prop) : (term231 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7609785 (x : nat) (y : nat) : (term286 x y) = (x = y).
Proof. exact (@lem7609784 (x = y)). Qed.
Lemma lem7609786 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7609787 (x : nat) (y : nat) : (term287 x y) = (term288 x y).
Proof. exact (MK_COMB (@lem7609786) (@lem7609785 x y)). Qed.
Lemma lem7609789 (a : Prop) : (term231 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7609790 (x : nat) (z : nat) : (term286 x z) = (x = z).
Proof. exact (@lem7609789 (x = z)). Qed.
Lemma lem7609791 (y : nat) (x : nat) (z : nat) : (term285 y x z) = (term289 y x z).
Proof. exact (MK_COMB (@lem7609787 x y) (@lem7609790 x z)). Qed.
Lemma lem7609792 (y : nat) (x : nat) (z : nat) : (term284 y x z) = (term289 y x z).
Proof. exact (TRANS (@lem7609782 y x z) (@lem7609791 y x z)). Qed.
Lemma lem7609793 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7609794 (y : nat) (x : nat) (z : nat) : (term290 y x z) = (term291 y x z).
Proof. exact (MK_COMB (@lem7609793) (@lem7609792 y x z)). Qed.
Lemma lem7609795 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7609796 (x : nat) (y : nat) (z : nat) : (term280 x y z) = (term292 x y z).
Proof. exact (MK_COMB (@lem7609794 y x z) (@lem7609795 y z)). Qed.
Lemma lem7609797 (x : nat) (y : nat) (z : nat) : (term277 y x z) = (term292 x y z).
Proof. exact (TRANS (@lem7609779 x y z) (@lem7609796 x y z)). Qed.
Lemma lem7609799 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term45 A) (h2 : term74 A i n' n) : term293 A n n'.
Proof. exact (conj (@lem7609623 A i n' n h2) (@lem7609686 A i n' n h1 h2)). Qed.
Lemma lem7609801 (x : nat) (y : nat) (z : nat) : term292 x y z.
Proof. exact (EQ_MP (@lem7609797 x y z) (@lem7609776 y x z)). Qed.
Lemma lem7609802 {A : Type'} (n : nat) (n' : nat) : term294 A n n'.
Proof. exact (@lem7609801 (term54 A n') (term54 A n) n'). Qed.
Lemma lem7609805 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term45 A) (h2 : term74 A i n' n) : (term54 A n) = n'.
Proof. exact (@lem7609802 A n n' (@lem7609799 A i n' n h1 h2)). Qed.
Lemma lem7609806 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term45 A) (h2 : term74 A i n' n) : term295 A n n'.
Proof. exact (fun h0 : term296 A n n' => @lem7609805 A i n' n h1 h2). Qed.
Lemma lem7609808 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7609809 {A : Type'} (n : nat) (n' : nat) : (term295 A n n') = ((term54 A n) = n').
Proof. exact (@lem7609808 ((term54 A n) = n')). Qed.
Lemma lem7609810 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term45 A) (h2 : term74 A i n' n) : (term54 A n) = n'.
Proof. exact (EQ_MP (@lem7609809 A n n') (@lem7609806 A i n' n h1 h2)). Qed.
Lemma lem7609812 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term74 A i n' n) : term29 A n.
Proof. exact (proj1 (@lem7608985 A i n' n h1)). Qed.
Lemma lem7609813 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term74 A i n' n) : term261 A n.
Proof. exact (fun h0 : term262 A n => @lem7609812 A i n' n h1). Qed.
Lemma lem7609815 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7609816 {A : Type'} (n : nat) : (term261 A n) = (term29 A n).
Proof. exact (@lem7609815 (term29 A n)). Qed.
Lemma lem7609817 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term74 A i n' n) : term29 A n.
Proof. exact (EQ_MP (@lem7609816 A n) (@lem7609813 A i n' n h1)). Qed.
Lemma lem7609819 {A : Type'} (_97858 : nat) (h1 : term45 A) : term270 A _97858.
Proof. exact (EQ_MP (@lem7609674 A _97858) (@lem7609663 A _97858 h1)). Qed.
Lemma lem7609820 {A : Type'} (n : nat) (h1 : term45 A) : term270 A n.
Proof. exact (@lem7609819 A n h1). Qed.
Lemma lem7609823 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term45 A) (h2 : term74 A i n' n) : (term54 A n) = n.
Proof. exact (@lem7609820 A n h1 (@lem7609817 A i n' n h2)). Qed.
Lemma lem7609824 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term45 A) (h2 : term74 A i n' n) : term271 A n.
Proof. exact (fun h0 : term240 A n => @lem7609823 A i n' n h1 h2). Qed.
Lemma lem7609826 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7609827 {A : Type'} (n : nat) : (term271 A n) = ((term54 A n) = n).
Proof. exact (@lem7609826 ((term54 A n) = n)). Qed.
Lemma lem7609828 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term45 A) (h2 : term74 A i n' n) : (term54 A n) = n.
Proof. exact (EQ_MP (@lem7609827 A n) (@lem7609824 A i n' n h1 h2)). Qed.
Lemma lem7609829 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term45 A) (h2 : term74 A i n' n) : term297 A n' n.
Proof. exact (conj (@lem7609810 A i n' n h1 h2) (@lem7609828 A i n' n h1 h2)). Qed.
Lemma lem7609831 (x : nat) (y : nat) (z : nat) : term292 x y z.
Proof. exact (EQ_MP (@lem7609797 x y z) (@lem7609776 y x z)). Qed.
Lemma lem7609832 {A : Type'} (n' : nat) (n : nat) : term298 A n' n.
Proof. exact (@lem7609831 (term54 A n) n' n). Qed.
Lemma lem7609835 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term45 A) (h2 : term74 A i n' n) : n' = n.
Proof. exact (@lem7609832 A n' n (@lem7609829 A i n' n h1 h2)). Qed.
Lemma lem7609836 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term45 A) (h2 : term74 A i n' n) : term299 n' n.
Proof. exact (fun h0 : term63 n' n => @lem7609835 A i n' n h1 h2). Qed.
Lemma lem7609838 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7609839 (n' : nat) (n : nat) : (term299 n' n) = (n' = n).
Proof. exact (@lem7609838 (n' = n)). Qed.
Lemma lem7609840 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term45 A) (h2 : term74 A i n' n) : n' = n.
Proof. exact (EQ_MP (@lem7609839 n' n) (@lem7609836 A i n' n h1 h2)). Qed.
Lemma lem7609843 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7609845 (n' : nat) (n : nat) : (term63 n' n) = (term300 n' n).
Proof. exact (@lem7609843 (n' = n)). Qed.
Lemma lem7609848 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term74 A i n' n) : term300 n' n.
Proof. exact (EQ_MP (@lem7609845 n' n) (@lem7609226 A i n' n h1)). Qed.
Lemma lem7609851 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term45 A) (h2 : term74 A i n' n) : False.
Proof. exact (@lem7609848 A i n' n h2 (@lem7609840 A i n' n h1 h2)). Qed.
Lemma lem7609852 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term45 A) (h2 : term74 A i n' n) : term254.
Proof. exact (fun h0 : ~ False => @lem7609851 A i n' n h1 h2). Qed.
Lemma lem7609854 (p : Prop) : (term224 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7609855 : term254 = False.
Proof. exact (@lem7609854 False). Qed.
Lemma lem7609857 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term45 A) (h2 : term74 A i n' n) : False.
Proof. exact (EQ_MP (@lem7609855) (@lem7609852 A i n' n h1 h2)). Qed.
Lemma lem7609858 {A : Type'} (i : finite_image A) (h1 : term87 A i) (h2 : term45 A) : (term87 A i) = False.
Proof. exact (prop_ext (fun h3 : term87 A i => @lem7609473 A i h1 h2) (fun h3 : False => @lem7609037 A i h1)). Qed.
Lemma lem7609859 {A : Type'} (i : finite_image A) (h1 : term87 A i) (h2 : term45 A) : False.
Proof. exact (EQ_MP (@lem7609858 A i h1 h2) (@lem7609037 A i h1)). Qed.
Lemma lem7609860 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term45 A) (h2 : term172 A i n' n) : False.
Proof. exact (or_elim (@lem7608977 A i n' n h2) (fun h0 : term87 A i => @lem7609859 A i h0 h1) (fun h0 : term74 A i n' n => @lem7609857 A i n' n h1 h0)). Qed.
Lemma lem7609861 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term45 A) (h2 : term172 A i n' n) : (term172 A i n' n) = False.
Proof. exact (prop_ext (fun h3 : term172 A i n' n => @lem7609860 A i n' n h1 h2) (fun h3 : False => @lem7608977 A i n' n h2)). Qed.
Lemma lem7609862 {A : Type'} (i : finite_image A) (n' : nat) (n : nat) (h1 : term45 A) (h2 : term172 A i n' n) : False.
Proof. exact (EQ_MP (@lem7609861 A i n' n h1 h2) (@lem7608977 A i n' n h2)). Qed.
Lemma lem7609863 {A : Type'} (i : finite_image A) (n : nat) (h1 : term175 A i n) (h2 : term45 A) : False.
Proof. exact (ex_elim (@lem7608794 A i n h1) (fun n' : nat => fun h0 : term174 A i n n' => @lem7609862 A i n' n h2 h0)). Qed.
Lemma lem7609864 {A : Type'} (i : finite_image A) (h1 : term177 A i) (h2 : term45 A) : False.
Proof. exact (ex_elim (@lem7608793 A i h1) (fun n : nat => fun h0 : term176 A i n => @lem7609863 A i n h0 h2)). Qed.
Lemma lem7609865 {A : Type'} (h1 : term44 A) (h2 : term45 A) : False.
Proof. exact (ex_elim (@lem7608634 A h1) (fun i : finite_image A => fun h0 : term178 A i => @lem7609864 A i h0 h2)). Qed.
Lemma lem7609866 {A : Type'} (h1 : term44 A) : term50 A.
Proof. exact (fun h0 : term45 A => @lem7609865 A h1 h0). Qed.
Lemma lem7609867 {A : Type'} : (term50 A) = (term51 A).
Proof. exact (@lem69 (term45 A)). Qed.
Lemma lem7609868 {A : Type'} (h1 : term44 A) : term51 A.
Proof. exact (EQ_MP (@lem7609867 A) (@lem7609866 A h1)). Qed.
Lemma lem7609869 {A : Type'} : term53 A.
Proof. exact (fun h0 : term44 A => @lem7609868 A h0). Qed.
Lemma lem7609870 {A : Type'} : term46 A.
Proof. exact (EQ_MP (@lem7608256 A) (@lem7609869 A)). Qed.
Lemma lem7609872 {A : Type'} : term46 A.
Proof. exact (@lem7608166 A (@lem7609870 A)). Qed.
Lemma lem7609873 {A : Type'} (h1 : term44 A) : term50 A.
Proof. exact (@lem7609872 A (@lem7608146 A h1)). Qed.
Lemma lem7609874 {A : Type'} (h1 : term44 A) : False.
Proof. exact (@lem7609873 A h1 (@lem7608147 A)). Qed.
Lemma lem7609875 {A : Type'} (h1 : term44 A) : (term44 A) = False.
Proof. exact (prop_ext (fun h2 : term44 A => @lem7609874 A h1) (fun h2 : False => @lem7608146 A h1)). Qed.
Lemma lem7609876 {A : Type'} (h1 : term44 A) : False.
Proof. exact (EQ_MP (@lem7609875 A h1) (@lem7608146 A h1)). Qed.
Lemma lem7609877 {A : Type'} : term43 A.
Proof. exact (fun h0 : term44 A => @lem7609876 A h0). Qed.
Lemma lem7609878 {A : Type'} : term41 A.
Proof. exact (EQ_MP (@lem7608145 A) (@lem7609877 A)). Qed.
Lemma lem7609879 {A : Type'} : term40 A.
Proof. exact (EQ_MP (@lem7608141 A) (@lem7609878 A)). Qed.
