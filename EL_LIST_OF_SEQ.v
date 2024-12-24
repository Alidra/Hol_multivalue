Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EL_LIST_OF_SEQ_term_abbrevs.
Require Import EL_APPEND_spec.
Require Import LENGTH_LIST_OF_SEQ_spec.
Require Import LT_REFL_spec.
Require Import SUB_REFL_spec.
Require Import SWAP_FORALL_THM_spec.
Require Import thm0_spec.
Require Import thm1094865_spec.
Require Import thm1094866_spec.
Require Import thm1105741_spec.
Require Import thm1105742_spec.
Require Import thm1111460_spec.
Require Import thm1111461_spec.
Require Import thm1111466_spec.
Require Import thm1111467_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm89994_spec.
Lemma lem1237098 {A : Type'} (s : nat -> A) : term0 A s.
Proof. exact (@lem1237097 A s). Qed.
Lemma lem1237099 {A : Type'} (s : nat -> A) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem1237100 {A : Type'} (s : nat -> A) : term1 A s.
Proof. exact (EQ_MP (@lem1237099 A s) (@lem1237098 A s)). Qed.
Lemma lem1237101 {A : Type'} (s : nat -> A) (n : nat) : term2 A s n.
Proof. exact (@lem1237100 A s n). Qed.
Lemma lem1237102 {A : Type'} (s : nat -> A) (n : nat) : (term2 A s n) = ((term3 A s n) = n).
Proof. exact (eq_refl (term2 A s n)). Qed.
Lemma lem1237104 {_28192 : Type'} (k : nat) : term4 _28192 k.
Proof. exact (@lem1206051 _28192 k). Qed.
Lemma lem1237105 {_28192 : Type'} (k : nat) : (term4 _28192 k) = (term5 _28192 k).
Proof. exact (eq_refl (term4 _28192 k)). Qed.
Lemma lem1237106 {_28192 : Type'} (k : nat) : term5 _28192 k.
Proof. exact (EQ_MP (@lem1237105 _28192 k) (@lem1237104 _28192 k)). Qed.
Lemma lem1237107 {_28192 : Type'} (k : nat) (l : list _28192) : term6 _28192 k l.
Proof. exact (@lem1237106 _28192 k l). Qed.
Lemma lem1237108 {_28192 : Type'} (k : nat) (l : list _28192) : (term6 _28192 k l) = (term7 _28192 k l).
Proof. exact (eq_refl (term6 _28192 k l)). Qed.
Lemma lem1237109 {_28192 : Type'} (k : nat) (l : list _28192) : term7 _28192 k l.
Proof. exact (EQ_MP (@lem1237108 _28192 k l) (@lem1237107 _28192 k l)). Qed.
Lemma lem1237110 {_28192 : Type'} (k : nat) (l : list _28192) (m : list _28192) : term8 _28192 k l m.
Proof. exact (@lem1237109 _28192 k l m). Qed.
Lemma lem1237111 {_28192 : Type'} (k : nat) (l : list _28192) (m : list _28192) : (term8 _28192 k l m) = ((term9 _28192 k l m) = (term10 _28192 k l m)).
Proof. exact (eq_refl (term8 _28192 k l m)). Qed.
Lemma lem1237113 : term11.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem1237114 (m : nat) : term12 m.
Proof. exact (@lem1237113 m). Qed.
Lemma lem1237115 (m : nat) : (term12 m) = (term13 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem1237116 (m : nat) : term13 m.
Proof. exact (EQ_MP (@lem1237115 m) (@lem1237114 m)). Qed.
Lemma lem1237117 (m : nat) (n : nat) : term14 m n.
Proof. exact (@lem1237116 m n). Qed.
Lemma lem1237118 (m : nat) (n : nat) : (term14 m n) = ((term15 m n) = (term16 m n)).
Proof. exact (eq_refl (term14 m n)). Qed.
Lemma lem1237120 : term17.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem1237121 (m : nat) : term18 m.
Proof. exact (@lem1237120 m). Qed.
Lemma lem1237122 (m : nat) : (term18 m) = ((term19 m) = False).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem1237126 {A B : Type'} (P : type1413 A B) : term20 A B P.
Proof. exact (@lem4792 A B P). Qed.
Lemma lem1237127 {A B : Type'} (P : type1413 A B) : (term20 A B P) = ((term21 A B P) = (term22 A B P)).
Proof. exact (eq_refl (term20 A B P)). Qed.
Lemma lem1237130 {A B : Type'} (P : type1413 A B) : (term21 A B P) = (term22 A B P).
Proof. exact (EQ_MP (@lem1237127 A B P) (@lem1237126 A B P)). Qed.
Lemma lem1237131 (P : type1605) : (term23 P) = (term24 P).
Proof. exact (@lem1237130 nat nat P). Qed.
Lemma lem1237132 {A : Type'} (s : nat -> A) : (term25 A s) = (term26 A s).
Proof. exact (@lem1237131 (term27 A s)). Qed.
Lemma lem1237133 {A : Type'} (s : nat -> A) (m : nat) : (term28 A s m) = (term29 A s m).
Proof. exact (eq_refl (term28 A s m)). Qed.
Lemma lem1237134 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1237135 {A : Type'} (s : nat -> A) (m : nat) (n : nat) : (term30 A s m n) = (term31 A s m n).
Proof. exact (MK_COMB (@lem1237133 A s m) (@lem1237134 n)). Qed.
Lemma lem1237136 {A : Type'} (n : nat) (s : nat -> A) (m : nat) : (term31 A s m n) = (term32 A n s m).
Proof. exact (eq_refl (term31 A s m n)). Qed.
Lemma lem1237137 {A : Type'} (n : nat) (s : nat -> A) (m : nat) : (term30 A s m n) = (term32 A n s m).
Proof. exact (TRANS (@lem1237135 A s m n) (@lem1237136 A n s m)). Qed.
Lemma lem1237138 {A : Type'} (s : nat -> A) (m : nat) : (term33 A s m) = (term29 A s m).
Proof. exact (fun_ext (fun n : nat => @lem1237137 A n s m)). Qed.
Lemma lem1237139 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1237140 {A : Type'} (s : nat -> A) (m : nat) : (term34 A s m) = (term35 A s m).
Proof. exact (MK_COMB (@lem1237139) (@lem1237138 A s m)). Qed.
Lemma lem1237141 {A : Type'} (s : nat -> A) : (term36 A s) = (term37 A s).
Proof. exact (fun_ext (fun m : nat => @lem1237140 A s m)). Qed.
Lemma lem1237142 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1237143 {A : Type'} (s : nat -> A) : (term25 A s) = (term38 A s).
Proof. exact (MK_COMB (@lem1237142) (@lem1237141 A s)). Qed.
Lemma lem1237144 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1237145 {A : Type'} (s : nat -> A) : (term39 A s) = (term40 A s).
Proof. exact (MK_COMB (@lem1237144) (@lem1237143 A s)). Qed.
Lemma lem1237146 {A : Type'} (s : nat -> A) (m : nat) : (term28 A s m) = (term29 A s m).
Proof. exact (eq_refl (term28 A s m)). Qed.
Lemma lem1237147 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1237148 {A : Type'} (s : nat -> A) (m : nat) (n : nat) : (term30 A s m n) = (term31 A s m n).
Proof. exact (MK_COMB (@lem1237146 A s m) (@lem1237147 n)). Qed.
Lemma lem1237149 {A : Type'} (n : nat) (s : nat -> A) (m : nat) : (term31 A s m n) = (term32 A n s m).
Proof. exact (eq_refl (term31 A s m n)). Qed.
Lemma lem1237150 {A : Type'} (n : nat) (s : nat -> A) (m : nat) : (term30 A s m n) = (term32 A n s m).
Proof. exact (TRANS (@lem1237148 A s m n) (@lem1237149 A n s m)). Qed.
Lemma lem1237151 {A : Type'} (n : nat) (s : nat -> A) : (term41 A s n) = (term42 A n s).
Proof. exact (fun_ext (fun m : nat => @lem1237150 A n s m)). Qed.
Lemma lem1237152 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1237153 {A : Type'} (n : nat) (s : nat -> A) : (term43 A s n) = (term44 A n s).
Proof. exact (MK_COMB (@lem1237152) (@lem1237151 A n s)). Qed.
Lemma lem1237154 {A : Type'} (s : nat -> A) : (term45 A s) = (term46 A s).
Proof. exact (fun_ext (fun n : nat => @lem1237153 A n s)). Qed.
Lemma lem1237155 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1237156 {A : Type'} (s : nat -> A) : (term26 A s) = (term47 A s).
Proof. exact (MK_COMB (@lem1237155) (@lem1237154 A s)). Qed.
Lemma lem1237157 {A : Type'} (s : nat -> A) : ((term25 A s) = (term26 A s)) = ((term38 A s) = (term47 A s)).
Proof. exact (MK_COMB (@lem1237145 A s) (@lem1237156 A s)). Qed.
Lemma lem1237158 {A : Type'} (s : nat -> A) : (term38 A s) = (term47 A s).
Proof. exact (EQ_MP (@lem1237157 A s) (@lem1237132 A s)). Qed.
Lemma lem1237159 {A : Type'} (s : nat -> A) : (term47 A s) = (term38 A s).
Proof. exact (SYM (@lem1237158 A s)). Qed.
Lemma lem1237161 (P : nat -> Prop) : term48 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1237162 {A : Type'} (s : nat -> A) : term49 A s.
Proof. exact (@lem1237161 (term46 A s)). Qed.
Lemma lem1237163 {A : Type'} (s : nat -> A) : (term50 A s) = (term51 A s).
Proof. exact (eq_refl (term50 A s)). Qed.
Lemma lem1237164 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1237165 {A : Type'} (s : nat -> A) : (term52 A s) = (term53 A s).
Proof. exact (MK_COMB (@lem1237164) (@lem1237163 A s)). Qed.
Lemma lem1237166 {A : Type'} (n : nat) (s : nat -> A) : (term54 A s n) = (term44 A n s).
Proof. exact (eq_refl (term54 A s n)). Qed.
Lemma lem1237167 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1237168 {A : Type'} (n : nat) (s : nat -> A) : (term55 A s n) = (term56 A n s).
Proof. exact (MK_COMB (@lem1237167) (@lem1237166 A n s)). Qed.
Lemma lem1237169 {A : Type'} (n : nat) (s : nat -> A) : (term57 A s n) = (term58 A n s).
Proof. exact (eq_refl (term57 A s n)). Qed.
Lemma lem1237170 {A : Type'} (n : nat) (s : nat -> A) : (term59 A s n) = (term60 A n s).
Proof. exact (MK_COMB (@lem1237168 A n s) (@lem1237169 A n s)). Qed.
Lemma lem1237171 {A : Type'} (s : nat -> A) : (term61 A s) = (term62 A s).
Proof. exact (fun_ext (fun n : nat => @lem1237170 A n s)). Qed.
Lemma lem1237172 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1237173 {A : Type'} (s : nat -> A) : (term63 A s) = (term64 A s).
Proof. exact (MK_COMB (@lem1237172) (@lem1237171 A s)). Qed.
Lemma lem1237174 {A : Type'} (s : nat -> A) : (term65 A s) = (term66 A s).
Proof. exact (MK_COMB (@lem1237165 A s) (@lem1237173 A s)). Qed.
Lemma lem1237175 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1237176 {A : Type'} (s : nat -> A) : (term67 A s) = (term68 A s).
Proof. exact (MK_COMB (@lem1237175) (@lem1237174 A s)). Qed.
Lemma lem1237177 {A : Type'} (n : nat) (s : nat -> A) : (term54 A s n) = (term44 A n s).
Proof. exact (eq_refl (term54 A s n)). Qed.
Lemma lem1237178 {A : Type'} (s : nat -> A) : (term69 A s) = (term46 A s).
Proof. exact (fun_ext (fun n : nat => @lem1237177 A n s)). Qed.
Lemma lem1237179 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1237180 {A : Type'} (s : nat -> A) : (term70 A s) = (term47 A s).
Proof. exact (MK_COMB (@lem1237179) (@lem1237178 A s)). Qed.
Lemma lem1237181 {A : Type'} (s : nat -> A) : (term49 A s) = (term71 A s).
Proof. exact (MK_COMB (@lem1237176 A s) (@lem1237180 A s)). Qed.
Lemma lem1237182 {A : Type'} (s : nat -> A) : term71 A s.
Proof. exact (EQ_MP (@lem1237181 A s) (@lem1237162 A s)). Qed.
Lemma lem1237183 {A : Type'} (n : nat) (s : nat -> A) (h1 : term44 A n s) : term44 A n s.
Proof. exact (h1). Qed.
Lemma lem1237191 (m : nat) : (term19 m) = False.
Proof. exact (EQ_MP (@lem1237122 m) (@lem1237121 m)). Qed.
Lemma lem1237192 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1237193 (m : nat) : (term72 m) = (imp False).
Proof. exact (MK_COMB (@lem1237192) (@lem1237191 m)). Qed.
Lemma lem1237197 {A : Type'} (s : nat -> A) : (term73 A s) = (@nil A).
Proof. exact (EQ_MP (@lem1111461 A s) (@lem1111460 A s)). Qed.
Lemma lem1237198 {A : Type'} (s : nat -> A) : (term73 A s) = (@nil A).
Proof. exact (@lem1237197 A s). Qed.
Lemma lem1237199 {A : Type'} (m : nat) : (@EL A m) = (@EL A m).
Proof. exact (eq_refl (@EL A m)). Qed.
Lemma lem1237200 {A : Type'} (s : nat -> A) (m : nat) : (term74 A m s) = (@EL A m (@nil A)).
Proof. exact (MK_COMB (@lem1237199 A m) (@lem1237198 A s)). Qed.
Lemma lem1237201 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1237202 {A : Type'} (s : nat -> A) (m : nat) : (term75 A m s) = (term76 A m).
Proof. exact (MK_COMB (@lem1237201 A) (@lem1237200 A s m)). Qed.
Lemma lem1237203 {A : Type'} (s : nat -> A) (m : nat) : (s m) = (s m).
Proof. exact (eq_refl (s m)). Qed.
Lemma lem1237204 {A : Type'} (s : nat -> A) (m : nat) : ((term74 A m s) = (s m)) = ((@EL A m (@nil A)) = (s m)).
Proof. exact (MK_COMB (@lem1237202 A s m) (@lem1237203 A s m)). Qed.
Lemma lem1237207 {A : Type'} (s : nat -> A) (m : nat) : (term77 A s m) = (term78 A s m).
Proof. exact (MK_COMB (@lem1237193 m) (@lem1237204 A s m)). Qed.
Lemma lem1237209 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1237210 {A : Type'} (s : nat -> A) (m : nat) : (term78 A s m) = True.
Proof. exact (@lem1237209 ((@EL A m (@nil A)) = (s m))). Qed.
Lemma lem1237211 {A : Type'} (s : nat -> A) (m : nat) : (term77 A s m) = True.
Proof. exact (TRANS (@lem1237207 A s m) (@lem1237210 A s m)). Qed.
Lemma lem1237212 {A : Type'} (s : nat -> A) : (term79 A s) = term80.
Proof. exact (fun_ext (fun m : nat => @lem1237211 A s m)). Qed.
Lemma lem1237213 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1237214 {A : Type'} (s : nat -> A) : (term51 A s) = term81.
Proof. exact (MK_COMB (@lem1237213) (@lem1237212 A s)). Qed.
Lemma lem1237216 {A : Type'} (t : Prop) : (term82 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1237217 (t : Prop) : (term83 t) = t.
Proof. exact (@lem1237216 nat t). Qed.
Lemma lem1237218 : term81 = True.
Proof. exact (@lem1237217 True). Qed.
Lemma lem1237219 {A : Type'} (s : nat -> A) : (term51 A s) = True.
Proof. exact (TRANS (@lem1237214 A s) (@lem1237218)). Qed.
Lemma lem1237220 {A : Type'} (s : nat -> A) : True = (term51 A s).
Proof. exact (SYM (@lem1237219 A s)). Qed.
Lemma lem1237221 {A : Type'} (s : nat -> A) : term51 A s.
Proof. exact (EQ_MP (@lem1237220 A s) (@lem0)). Qed.
Lemma lem1237229 (m : nat) (n : nat) : (term15 m n) = (term16 m n).
Proof. exact (EQ_MP (@lem1237118 m n) (@lem1237117 m n)). Qed.
Lemma lem1237234 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1237235 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (MK_COMB (@lem1237234) (@lem1237229 m n)). Qed.
Lemma lem1237239 {A : Type'} (s : nat -> A) (n : nat) : (term86 A s n) = (term87 A s n).
Proof. exact (EQ_MP (@lem1111467 A s n) (@lem1111466 A s n)). Qed.
Lemma lem1237240 {A : Type'} (s : nat -> A) (n : nat) : (term86 A s n) = (term87 A s n).
Proof. exact (@lem1237239 A s n). Qed.
Lemma lem1237241 {A : Type'} (m : nat) : (@EL A m) = (@EL A m).
Proof. exact (eq_refl (@EL A m)). Qed.
Lemma lem1237242 {A : Type'} (m : nat) (s : nat -> A) (n : nat) : (term88 A m s n) = (term89 A m s n).
Proof. exact (MK_COMB (@lem1237241 A m) (@lem1237240 A s n)). Qed.
Lemma lem1237244 {_28192 : Type'} (k : nat) (l : list _28192) (m : list _28192) : (term9 _28192 k l m) = (term10 _28192 k l m).
Proof. exact (EQ_MP (@lem1237111 _28192 k l m) (@lem1237110 _28192 k l m)). Qed.
Lemma lem1237245 {A : Type'} (k : nat) (l : list A) (m : list A) : (term9 A k l m) = (term10 A k l m).
Proof. exact (@lem1237244 A k l m). Qed.
Lemma lem1237246 {A : Type'} (m : nat) (s : nat -> A) (n : nat) : (term89 A m s n) = (term90 A m s n).
Proof. exact (@lem1237245 A m (@list_of_seq A s n) (term91 A s n)). Qed.
Lemma lem1237248 {A : Type'} (s : nat -> A) (n : nat) : (term3 A s n) = n.
Proof. exact (EQ_MP (@lem1237102 A s n) (@lem1237101 A s n)). Qed.
Lemma lem1237249 {A : Type'} (s : nat -> A) (n : nat) : (term3 A s n) = n.
Proof. exact (@lem1237248 A s n). Qed.
Lemma lem1237250 (m : nat) : (Peano.lt m) = (Peano.lt m).
Proof. exact (eq_refl (Peano.lt m)). Qed.
Lemma lem1237251 {A : Type'} (s : nat -> A) (m : nat) (n : nat) : (term92 A m s n) = (Peano.lt m n).
Proof. exact (MK_COMB (@lem1237250 m) (@lem1237249 A s n)). Qed.
Lemma lem1237252 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem1237253 {A : Type'} (s : nat -> A) (m : nat) (n : nat) : (term93 A m s n) = (term94 A m n).
Proof. exact (MK_COMB (@lem1237252 A) (@lem1237251 A s m n)). Qed.
Lemma lem1237254 {A : Type'} (m : nat) (s : nat -> A) (n : nat) : (term95 A m s n) = (term95 A m s n).
Proof. exact (eq_refl (term95 A m s n)). Qed.
Lemma lem1237255 {A : Type'} (m : nat) (s : nat -> A) (n : nat) : (term96 A m s n) = (term97 A m s n).
Proof. exact (MK_COMB (@lem1237253 A s m n) (@lem1237254 A m s n)). Qed.
Lemma lem1237257 {A : Type'} (s : nat -> A) (n : nat) : (term3 A s n) = n.
Proof. exact (EQ_MP (@lem1237102 A s n) (@lem1237101 A s n)). Qed.
Lemma lem1237258 {A : Type'} (s : nat -> A) (n : nat) : (term3 A s n) = n.
Proof. exact (@lem1237257 A s n). Qed.
Lemma lem1237259 (m : nat) : (Nat.sub m) = (Nat.sub m).
Proof. exact (eq_refl (Nat.sub m)). Qed.
Lemma lem1237260 {A : Type'} (s : nat -> A) (m : nat) (n : nat) : (term98 A m s n) = (Nat.sub m n).
Proof. exact (MK_COMB (@lem1237259 m) (@lem1237258 A s n)). Qed.
Lemma lem1237261 {A : Type'} : (@EL A) = (@EL A).
Proof. exact (eq_refl (@EL A)). Qed.
Lemma lem1237262 {A : Type'} (s : nat -> A) (m : nat) (n : nat) : (term99 A m s n) = (term100 A m n).
Proof. exact (MK_COMB (@lem1237261 A) (@lem1237260 A s m n)). Qed.
Lemma lem1237263 {A : Type'} (s : nat -> A) (n : nat) : (term91 A s n) = (term91 A s n).
Proof. exact (eq_refl (term91 A s n)). Qed.
Lemma lem1237264 {A : Type'} (m : nat) (s : nat -> A) (n : nat) : (term101 A m s n) = (term102 A m s n).
Proof. exact (MK_COMB (@lem1237262 A s m n) (@lem1237263 A s n)). Qed.
Lemma lem1237265 {A : Type'} (m : nat) (s : nat -> A) (n : nat) : (term90 A m s n) = (term103 A m s n).
Proof. exact (MK_COMB (@lem1237255 A m s n) (@lem1237264 A m s n)). Qed.
Lemma lem1237266 {A : Type'} (m : nat) (s : nat -> A) (n : nat) : (term89 A m s n) = (term103 A m s n).
Proof. exact (TRANS (@lem1237246 A m s n) (@lem1237265 A m s n)). Qed.
Lemma lem1237267 {A : Type'} (m : nat) (s : nat -> A) (n : nat) : (term88 A m s n) = (term103 A m s n).
Proof. exact (TRANS (@lem1237242 A m s n) (@lem1237266 A m s n)). Qed.
Lemma lem1237268 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1237269 {A : Type'} (m : nat) (s : nat -> A) (n : nat) : (term104 A m s n) = (term105 A m s n).
Proof. exact (MK_COMB (@lem1237268 A) (@lem1237267 A m s n)). Qed.
Lemma lem1237270 {A : Type'} (s : nat -> A) (m : nat) : (s m) = (s m).
Proof. exact (eq_refl (s m)). Qed.
Lemma lem1237271 {A : Type'} (n : nat) (s : nat -> A) (m : nat) : ((term88 A m s n) = (s m)) = ((term103 A m s n) = (s m)).
Proof. exact (MK_COMB (@lem1237269 A m s n) (@lem1237270 A s m)). Qed.
Lemma lem1237274 {A : Type'} (n : nat) (s : nat -> A) (m : nat) : (term106 A n s m) = (term107 A n s m).
Proof. exact (MK_COMB (@lem1237235 m n) (@lem1237271 A n s m)). Qed.
Lemma lem1237277 {A : Type'} (n : nat) (s : nat -> A) : (term108 A n s) = (term109 A n s).
Proof. exact (fun_ext (fun m : nat => @lem1237274 A n s m)). Qed.
Lemma lem1237278 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1237279 {A : Type'} (n : nat) (s : nat -> A) : (term58 A n s) = (term110 A n s).
Proof. exact (MK_COMB (@lem1237278) (@lem1237277 A n s)). Qed.
Lemma lem1237284 {A : Type'} (n : nat) (s : nat -> A) : (term110 A n s) = (term58 A n s).
Proof. exact (SYM (@lem1237279 A n s)). Qed.
Lemma lem1237285 (m : nat) (n : nat) (h1 : term16 m n) : term16 m n.
Proof. exact (h1). Qed.
Lemma lem1237286 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem1237287 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem1237288 (n : nat) : term111 n.
Proof. exact (@lem91686 n). Qed.
Lemma lem1237289 (n : nat) : (term111 n) = (term112 n).
Proof. exact (eq_refl (term111 n)). Qed.
Lemma lem1237290 (n : nat) : term112 n.
Proof. exact (EQ_MP (@lem1237289 n) (@lem1237288 n)). Qed.
Lemma lem1237291 (n : nat) : term113 n.
Proof. exact (@lem82 (Peano.lt n n)). Qed.
Lemma lem1237295 (n : nat) : term114 n.
Proof. exact (@lem135734 n). Qed.
Lemma lem1237296 (n : nat) : (term114 n) = ((Nat.sub n n) = (NUMERAL 0)).
Proof. exact (eq_refl (term114 n)). Qed.
Lemma lem1237298 {A : Type'} (m : nat) (n : nat) (s : nat -> A) (h1 : term44 A n s) : term115 A n s m.
Proof. exact (@lem1237183 A n s h1 m). Qed.
Lemma lem1237299 {A : Type'} (n : nat) (s : nat -> A) (m : nat) : (term115 A n s m) = (term32 A n s m).
Proof. exact (eq_refl (term115 A n s m)). Qed.
Lemma lem1237300 {A : Type'} (m : nat) (n : nat) (s : nat -> A) (h1 : term44 A n s) : term32 A n s m.
Proof. exact (EQ_MP (@lem1237299 A n s m) (@lem1237298 A m n s h1)). Qed.
Lemma lem1237301 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem1237302 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : Peano.lt m n) : (term95 A m s n) = (s m).
Proof. exact (@lem1237300 A m n s h1 (@lem1237301 m n h2)). Qed.
Lemma lem1237311 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term116 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem1237312 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term117 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem1237311 _2963 g t e g' t' e'). Qed.
Lemma lem1237313 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term118 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem1237312 _2963 g t e g' t'). Qed.
Lemma lem1237314 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term119 _2963 g t e.
Proof. exact (fun g' : Prop => @lem1237313 _2963 g t e g'). Qed.
Lemma lem1237315 {A : Type'} (g : Prop) (t : A) (e : A) : term119 A g t e.
Proof. exact (@lem1237314 A g t e). Qed.
Lemma lem1237316 {A : Type'} (m : nat) (s : nat -> A) (n : nat) : term120 A m s n.
Proof. exact (@lem1237315 A (Peano.lt m n) (term95 A m s n) (term102 A m s n)). Qed.
Lemma lem1237317 {A : Type'} (m : nat) (s : nat -> A) (n : nat) (g' : Prop) : term121 A m s n g'.
Proof. exact (@lem1237316 A m s n g'). Qed.
Lemma lem1237318 {A : Type'} (m : nat) (s : nat -> A) (n : nat) (g' : Prop) : (term121 A m s n g') = (term122 A m s n g').
Proof. exact (eq_refl (term121 A m s n g')). Qed.
Lemma lem1237319 {A : Type'} (m : nat) (s : nat -> A) (n : nat) (g' : Prop) : term122 A m s n g'.
Proof. exact (EQ_MP (@lem1237318 A m s n g') (@lem1237317 A m s n g')). Qed.
Lemma lem1237320 {A : Type'} (m : nat) (s : nat -> A) (n : nat) (g' : Prop) (t' : A) : term123 A m s n g' t'.
Proof. exact (@lem1237319 A m s n g' t'). Qed.
Lemma lem1237321 {A : Type'} (m : nat) (s : nat -> A) (n : nat) (g' : Prop) (t' : A) : (term123 A m s n g' t') = (term124 A m s n g' t').
Proof. exact (eq_refl (term123 A m s n g' t')). Qed.
Lemma lem1237322 {A : Type'} (m : nat) (s : nat -> A) (n : nat) (g' : Prop) (t' : A) : term124 A m s n g' t'.
Proof. exact (EQ_MP (@lem1237321 A m s n g' t') (@lem1237320 A m s n g' t')). Qed.
Lemma lem1237323 {A : Type'} (m : nat) (s : nat -> A) (n : nat) (g' : Prop) (t' : A) (e' : A) : term125 A m s n g' t' e'.
Proof. exact (@lem1237322 A m s n g' t' e'). Qed.
Lemma lem1237324 {A : Type'} (m : nat) (s : nat -> A) (n : nat) (g' : Prop) (t' : A) (e' : A) : (term125 A m s n g' t' e') = (term126 A m s n g' t' e').
Proof. exact (eq_refl (term125 A m s n g' t' e')). Qed.
Lemma lem1237325 {A : Type'} (m : nat) (s : nat -> A) (n : nat) (g' : Prop) (t' : A) (e' : A) : term126 A m s n g' t' e'.
Proof. exact (EQ_MP (@lem1237324 A m s n g' t' e') (@lem1237323 A m s n g' t' e')). Qed.
Lemma lem1237329 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem1237330 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem1237331 (m : nat) (n : nat) (h1 : m = n) : (Peano.lt m) = (Peano.lt n).
Proof. exact (MK_COMB (@lem1237330) (@lem1237329 m n h1)). Qed.
Lemma lem1237332 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1237333 (m : nat) (n : nat) (h1 : m = n) : (Peano.lt m n) = (Peano.lt n n).
Proof. exact (MK_COMB (@lem1237331 m n h1) (@lem1237332 n)). Qed.
Lemma lem1237335 (n : nat) : (Peano.lt n n) = False.
Proof. exact (@lem1237291 n (@lem1237290 n)). Qed.
Lemma lem1237336 (m : nat) (n : nat) (h1 : m = n) : (Peano.lt m n) = False.
Proof. exact (TRANS (@lem1237333 m n h1) (@lem1237335 n)). Qed.
Lemma lem1237337 {A : Type'} (m : nat) (s : nat -> A) (n : nat) (t' : A) (e' : A) : term127 A m s n t' e'.
Proof. exact (@lem1237325 A m s n False t' e'). Qed.
Lemma lem1237338 {A : Type'} (s : nat -> A) (t' : A) (e' : A) (m : nat) (n : nat) (h1 : m = n) : term128 A m s n t' e'.
Proof. exact (@lem1237337 A m s n t' e' (@lem1237336 m n h1)). Qed.
Lemma lem1237339 (h1 : False) : False.
Proof. exact (h1). Qed.
Lemma lem1237340 : False = (False = True).
Proof. exact (@lem7 False). Qed.
Lemma lem1237343 {A : Type'} (m : nat) (n : nat) (s : nat -> A) (h1 : term44 A n s) : term32 A n s m.
Proof. exact (fun h0 : Peano.lt m n => @lem1237302 A s m n h1 h0). Qed.
Lemma lem1237347 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem1237348 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem1237349 (m : nat) (n : nat) (h1 : m = n) : (Peano.lt m) = (Peano.lt n).
Proof. exact (MK_COMB (@lem1237348) (@lem1237347 m n h1)). Qed.
Lemma lem1237350 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1237351 (m : nat) (n : nat) (h1 : m = n) : (Peano.lt m n) = (Peano.lt n n).
Proof. exact (MK_COMB (@lem1237349 m n h1) (@lem1237350 n)). Qed.
Lemma lem1237353 (n : nat) : (Peano.lt n n) = False.
Proof. exact (@lem1237291 n (@lem1237290 n)). Qed.
Lemma lem1237355 (h1 : False) : False = True.
Proof. exact (EQ_MP (@lem1237340) (@lem1237339 h1)). Qed.
Lemma lem1237356 (n : nat) (h1 : False) : (Peano.lt n n) = True.
Proof. exact (TRANS (@lem1237353 n) (@lem1237355 h1)). Qed.
Lemma lem1237357 (m : nat) (n : nat) (h1 : False) (h2 : m = n) : (Peano.lt m n) = True.
Proof. exact (TRANS (@lem1237351 m n h2) (@lem1237356 n h1)). Qed.
Lemma lem1237358 (m : nat) (n : nat) (h1 : False) (h2 : m = n) : True = (Peano.lt m n).
Proof. exact (SYM (@lem1237357 m n h1 h2)). Qed.
Lemma lem1237359 (m : nat) (n : nat) (h1 : False) (h2 : m = n) : Peano.lt m n.
Proof. exact (EQ_MP (@lem1237358 m n h1 h2) (@lem0)). Qed.
Lemma lem1237360 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : False) (h2 : term44 A n s) (h3 : m = n) : (term95 A m s n) = (s m).
Proof. exact (@lem1237343 A m n s h2 (@lem1237359 m n h1 h3)). Qed.
Lemma lem1237362 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem1237363 {A : Type'} (s : nat -> A) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem1237364 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : m = n) : (s m) = (s n).
Proof. exact (MK_COMB (@lem1237363 A s) (@lem1237362 m n h1)). Qed.
Lemma lem1237365 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : False) (h2 : term44 A n s) (h3 : m = n) : (term95 A m s n) = (s n).
Proof. exact (TRANS (@lem1237360 A s m n h1 h2 h3) (@lem1237364 A s m n h3)). Qed.
Lemma lem1237366 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : m = n) : term129 A m s n.
Proof. exact (fun h0 : False => @lem1237365 A s m n h0 h1 h2). Qed.
Lemma lem1237367 {A : Type'} (s : nat -> A) (e' : A) (m : nat) (n : nat) (h1 : m = n) : term130 A m s n e'.
Proof. exact (@lem1237338 A s (s n) e' m n h1). Qed.
Lemma lem1237368 {A : Type'} (e' : A) (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : m = n) : term131 A m s n e'.
Proof. exact (@lem1237367 A s e' m n h2 (@lem1237366 A s m n h1 h2)). Qed.
Lemma lem1237377 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem1237378 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem1237379 (m : nat) (n : nat) (h1 : m = n) : (Nat.sub m) = (Nat.sub n).
Proof. exact (MK_COMB (@lem1237378) (@lem1237377 m n h1)). Qed.
Lemma lem1237380 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1237381 (m : nat) (n : nat) (h1 : m = n) : (Nat.sub m n) = (Nat.sub n n).
Proof. exact (MK_COMB (@lem1237379 m n h1) (@lem1237380 n)). Qed.
Lemma lem1237383 (n : nat) : (Nat.sub n n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1237296 n) (@lem1237295 n)). Qed.
Lemma lem1237384 (m : nat) (n : nat) (h1 : m = n) : (Nat.sub m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem1237381 m n h1) (@lem1237383 n)). Qed.
Lemma lem1237385 {A : Type'} : (@EL A) = (@EL A).
Proof. exact (eq_refl (@EL A)). Qed.
Lemma lem1237386 {A : Type'} (m : nat) (n : nat) (h1 : m = n) : (term100 A m n) = (term132 A).
Proof. exact (MK_COMB (@lem1237385 A) (@lem1237384 m n h1)). Qed.
Lemma lem1237387 {A : Type'} (s : nat -> A) (n : nat) : (term91 A s n) = (term91 A s n).
Proof. exact (eq_refl (term91 A s n)). Qed.
Lemma lem1237388 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : m = n) : (term102 A m s n) = (term133 A s n).
Proof. exact (MK_COMB (@lem1237386 A m n h1) (@lem1237387 A s n)). Qed.
Lemma lem1237390 {_25569 : Type'} (l : list _25569) : (term134 _25569 l) = (@hd _25569 l).
Proof. exact (EQ_MP (@lem1105742 _25569 l) (@lem1105741 _25569 l)). Qed.
Lemma lem1237391 {A : Type'} (l : list A) : (term134 A l) = (@hd A l).
Proof. exact (@lem1237390 A l). Qed.
Lemma lem1237392 {A : Type'} (s : nat -> A) (n : nat) : (term133 A s n) = (term135 A s n).
Proof. exact (@lem1237391 A (term91 A s n)). Qed.
Lemma lem1237394 {A : Type'} (t : list A) (h : A) : (term136 A h t) = h.
Proof. exact (EQ_MP (@lem1094866 A t h) (@lem1094865 A t h)). Qed.
Lemma lem1237395 {A : Type'} (t : list A) (h : A) : (term136 A h t) = h.
Proof. exact (@lem1237394 A t h). Qed.
Lemma lem1237396 {A : Type'} (s : nat -> A) (n : nat) : (term135 A s n) = (s n).
Proof. exact (@lem1237395 A (@nil A) (s n)). Qed.
Lemma lem1237397 {A : Type'} (s : nat -> A) (n : nat) : (term133 A s n) = (s n).
Proof. exact (TRANS (@lem1237392 A s n) (@lem1237396 A s n)). Qed.
Lemma lem1237398 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : m = n) : (term102 A m s n) = (s n).
Proof. exact (TRANS (@lem1237388 A s m n h1) (@lem1237397 A s n)). Qed.
Lemma lem1237399 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : m = n) : term137 A m s n.
Proof. exact (fun h0 : ~ False => @lem1237398 A s m n h1). Qed.
Lemma lem1237400 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : m = n) : term138 A m s n.
Proof. exact (@lem1237368 A (s n) s m n h1 h2). Qed.
Lemma lem1237401 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : m = n) : (term103 A m s n) = (term139 A s n).
Proof. exact (@lem1237400 A s m n h1 h2 (@lem1237399 A s m n h2)). Qed.
Lemma lem1237403 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1237404 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem1237403 A t1 t2). Qed.
Lemma lem1237405 {A : Type'} (s : nat -> A) (n : nat) : (term139 A s n) = (s n).
Proof. exact (@lem1237404 A (s n) (s n)). Qed.
Lemma lem1237406 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : m = n) : (term103 A m s n) = (s n).
Proof. exact (TRANS (@lem1237401 A s m n h1 h2) (@lem1237405 A s n)). Qed.
Lemma lem1237407 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1237408 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : m = n) : (term105 A m s n) = (term140 A s n).
Proof. exact (MK_COMB (@lem1237407 A) (@lem1237406 A s m n h1 h2)). Qed.
Lemma lem1237410 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem1237411 {A : Type'} (s : nat -> A) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem1237412 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : m = n) : (s m) = (s n).
Proof. exact (MK_COMB (@lem1237411 A s) (@lem1237410 m n h1)). Qed.
Lemma lem1237413 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : m = n) : ((term103 A m s n) = (s m)) = ((s n) = (s n)).
Proof. exact (MK_COMB (@lem1237408 A s m n h1 h2) (@lem1237412 A s m n h2)). Qed.
Lemma lem1237415 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1237416 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1237415 A x). Qed.
Lemma lem1237417 {A : Type'} (s : nat -> A) (n : nat) : ((s n) = (s n)) = True.
Proof. exact (@lem1237416 A (s n)). Qed.
Lemma lem1237418 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : m = n) : ((term103 A m s n) = (s m)) = True.
Proof. exact (TRANS (@lem1237413 A s m n h1 h2) (@lem1237417 A s n)). Qed.
Lemma lem1237419 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : m = n) : True = ((term103 A m s n) = (s m)).
Proof. exact (SYM (@lem1237418 A s m n h1 h2)). Qed.
Lemma lem1237420 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : m = n) : (term103 A m s n) = (s m).
Proof. exact (EQ_MP (@lem1237419 A s m n h1 h2) (@lem0)). Qed.
Lemma lem1237431 {A : Type'} (m : nat) (n : nat) (s : nat -> A) (h1 : term44 A n s) : term115 A n s m.
Proof. exact (@lem1237183 A n s h1 m). Qed.
Lemma lem1237432 {A : Type'} (n : nat) (s : nat -> A) (m : nat) : (term115 A n s m) = (term32 A n s m).
Proof. exact (eq_refl (term115 A n s m)). Qed.
Lemma lem1237433 {A : Type'} (m : nat) (n : nat) (s : nat -> A) (h1 : term44 A n s) : term32 A n s m.
Proof. exact (EQ_MP (@lem1237432 A n s m) (@lem1237431 A m n s h1)). Qed.
Lemma lem1237434 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem1237435 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : Peano.lt m n) : (term95 A m s n) = (s m).
Proof. exact (@lem1237433 A m n s h1 (@lem1237434 m n h2)). Qed.
Lemma lem1237441 (m : nat) (n : nat) : (Peano.lt m n) = ((Peano.lt m n) = True).
Proof. exact (@lem7 (Peano.lt m n)). Qed.
Lemma lem1237446 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term116 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem1237447 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term117 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem1237446 _2963 g t e g' t' e'). Qed.
Lemma lem1237448 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term118 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem1237447 _2963 g t e g' t'). Qed.
Lemma lem1237449 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term119 _2963 g t e.
Proof. exact (fun g' : Prop => @lem1237448 _2963 g t e g'). Qed.
Lemma lem1237450 {A : Type'} (g : Prop) (t : A) (e : A) : term119 A g t e.
Proof. exact (@lem1237449 A g t e). Qed.
Lemma lem1237451 {A : Type'} (m : nat) (s : nat -> A) (n : nat) : term120 A m s n.
Proof. exact (@lem1237450 A (Peano.lt m n) (term95 A m s n) (term102 A m s n)). Qed.
Lemma lem1237452 {A : Type'} (m : nat) (s : nat -> A) (n : nat) (g' : Prop) : term121 A m s n g'.
Proof. exact (@lem1237451 A m s n g'). Qed.
Lemma lem1237453 {A : Type'} (m : nat) (s : nat -> A) (n : nat) (g' : Prop) : (term121 A m s n g') = (term122 A m s n g').
Proof. exact (eq_refl (term121 A m s n g')). Qed.
Lemma lem1237454 {A : Type'} (m : nat) (s : nat -> A) (n : nat) (g' : Prop) : term122 A m s n g'.
Proof. exact (EQ_MP (@lem1237453 A m s n g') (@lem1237452 A m s n g')). Qed.
Lemma lem1237455 {A : Type'} (m : nat) (s : nat -> A) (n : nat) (g' : Prop) (t' : A) : term123 A m s n g' t'.
Proof. exact (@lem1237454 A m s n g' t'). Qed.
Lemma lem1237456 {A : Type'} (m : nat) (s : nat -> A) (n : nat) (g' : Prop) (t' : A) : (term123 A m s n g' t') = (term124 A m s n g' t').
Proof. exact (eq_refl (term123 A m s n g' t')). Qed.
Lemma lem1237457 {A : Type'} (m : nat) (s : nat -> A) (n : nat) (g' : Prop) (t' : A) : term124 A m s n g' t'.
Proof. exact (EQ_MP (@lem1237456 A m s n g' t') (@lem1237455 A m s n g' t')). Qed.
Lemma lem1237458 {A : Type'} (m : nat) (s : nat -> A) (n : nat) (g' : Prop) (t' : A) (e' : A) : term125 A m s n g' t' e'.
Proof. exact (@lem1237457 A m s n g' t' e'). Qed.
Lemma lem1237459 {A : Type'} (m : nat) (s : nat -> A) (n : nat) (g' : Prop) (t' : A) (e' : A) : (term125 A m s n g' t' e') = (term126 A m s n g' t' e').
Proof. exact (eq_refl (term125 A m s n g' t' e')). Qed.
Lemma lem1237460 {A : Type'} (m : nat) (s : nat -> A) (n : nat) (g' : Prop) (t' : A) (e' : A) : term126 A m s n g' t' e'.
Proof. exact (EQ_MP (@lem1237459 A m s n g' t' e') (@lem1237458 A m s n g' t' e')). Qed.
Lemma lem1237462 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Peano.lt m n) = True.
Proof. exact (EQ_MP (@lem1237441 m n) (@lem1237287 m n h1)). Qed.
Lemma lem1237463 {A : Type'} (m : nat) (s : nat -> A) (n : nat) (t' : A) (e' : A) : term141 A m s n t' e'.
Proof. exact (@lem1237460 A m s n True t' e'). Qed.
Lemma lem1237464 {A : Type'} (s : nat -> A) (t' : A) (e' : A) (m : nat) (n : nat) (h1 : Peano.lt m n) : term142 A m s n t' e'.
Proof. exact (@lem1237463 A m s n t' e' (@lem1237462 m n h1)). Qed.
Lemma lem1237471 {A : Type'} (m : nat) (n : nat) (s : nat -> A) (h1 : term44 A n s) : term32 A n s m.
Proof. exact (fun h0 : Peano.lt m n => @lem1237435 A s m n h1 h0). Qed.
Lemma lem1237473 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Peano.lt m n) = True.
Proof. exact (EQ_MP (@lem1237441 m n) (@lem1237287 m n h1)). Qed.
Lemma lem1237476 (m : nat) (n : nat) (h1 : Peano.lt m n) : True = (Peano.lt m n).
Proof. exact (SYM (@lem1237473 m n h1)). Qed.
Lemma lem1237477 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (EQ_MP (@lem1237476 m n h1) (@lem0)). Qed.
Lemma lem1237478 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : Peano.lt m n) : (term95 A m s n) = (s m).
Proof. exact (@lem1237471 A m n s h1 (@lem1237477 m n h2)). Qed.
Lemma lem1237479 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : Peano.lt m n) : term143 A n s m.
Proof. exact (fun h0 : True => @lem1237478 A s m n h1 h2). Qed.
Lemma lem1237480 {A : Type'} (s : nat -> A) (e' : A) (m : nat) (n : nat) (h1 : Peano.lt m n) : term144 A n s m e'.
Proof. exact (@lem1237464 A s (s m) e' m n h1). Qed.
Lemma lem1237481 {A : Type'} (e' : A) (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : Peano.lt m n) : term145 A n s m e'.
Proof. exact (@lem1237480 A s e' m n h2 (@lem1237479 A s m n h1 h2)). Qed.
Lemma lem1237487 {A : Type'} (m : nat) (s : nat -> A) (n : nat) : (term102 A m s n) = (term102 A m s n).
Proof. exact (eq_refl (term102 A m s n)). Qed.
Lemma lem1237488 {A : Type'} (m : nat) (s : nat -> A) (n : nat) : term146 A m s n.
Proof. exact (fun h0 : ~ True => @lem1237487 A m s n). Qed.
Lemma lem1237489 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : Peano.lt m n) : term147 A m s n.
Proof. exact (@lem1237481 A (term102 A m s n) s m n h1 h2). Qed.
Lemma lem1237490 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : Peano.lt m n) : (term103 A m s n) = (term148 A m s n).
Proof. exact (@lem1237489 A s m n h1 h2 (@lem1237488 A m s n)). Qed.
Lemma lem1237492 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1237493 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem1237492 A t2 t1). Qed.
Lemma lem1237494 {A : Type'} (n : nat) (s : nat -> A) (m : nat) : (term148 A m s n) = (s m).
Proof. exact (@lem1237493 A (term102 A m s n) (s m)). Qed.
Lemma lem1237495 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : Peano.lt m n) : (term103 A m s n) = (s m).
Proof. exact (TRANS (@lem1237490 A s m n h1 h2) (@lem1237494 A n s m)). Qed.
Lemma lem1237496 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1237497 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : Peano.lt m n) : (term105 A m s n) = (term140 A s m).
Proof. exact (MK_COMB (@lem1237496 A) (@lem1237495 A s m n h1 h2)). Qed.
Lemma lem1237498 {A : Type'} (s : nat -> A) (m : nat) : (s m) = (s m).
Proof. exact (eq_refl (s m)). Qed.
Lemma lem1237499 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : Peano.lt m n) : ((term103 A m s n) = (s m)) = ((s m) = (s m)).
Proof. exact (MK_COMB (@lem1237497 A s m n h1 h2) (@lem1237498 A s m)). Qed.
Lemma lem1237501 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1237502 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1237501 A x). Qed.
Lemma lem1237503 {A : Type'} (s : nat -> A) (m : nat) : ((s m) = (s m)) = True.
Proof. exact (@lem1237502 A (s m)). Qed.
Lemma lem1237504 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : Peano.lt m n) : ((term103 A m s n) = (s m)) = True.
Proof. exact (TRANS (@lem1237499 A s m n h1 h2) (@lem1237503 A s m)). Qed.
Lemma lem1237505 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : Peano.lt m n) : True = ((term103 A m s n) = (s m)).
Proof. exact (SYM (@lem1237504 A s m n h1 h2)). Qed.
Lemma lem1237506 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : Peano.lt m n) : (term103 A m s n) = (s m).
Proof. exact (EQ_MP (@lem1237505 A s m n h1 h2) (@lem0)). Qed.
Lemma lem1237507 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : Peano.lt m n) : (Peano.lt m n) = ((term103 A m s n) = (s m)).
Proof. exact (prop_ext (fun h3 : Peano.lt m n => @lem1237506 A s m n h1 h2) (fun h3 : (term103 A m s n) = (s m) => @lem1237287 m n h2)). Qed.
Lemma lem1237508 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : Peano.lt m n) : (term103 A m s n) = (s m).
Proof. exact (EQ_MP (@lem1237507 A s m n h1 h2) (@lem1237287 m n h2)). Qed.
Lemma lem1237509 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : m = n) : (m = n) = ((term103 A m s n) = (s m)).
Proof. exact (prop_ext (fun h3 : m = n => @lem1237420 A s m n h1 h2) (fun h3 : (term103 A m s n) = (s m) => @lem1237286 m n h2)). Qed.
Lemma lem1237510 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : m = n) : (term103 A m s n) = (s m).
Proof. exact (EQ_MP (@lem1237509 A s m n h1 h2) (@lem1237286 m n h2)). Qed.
Lemma lem1237511 {A : Type'} (s : nat -> A) (m : nat) (n : nat) (h1 : term44 A n s) (h2 : term16 m n) : (term103 A m s n) = (s m).
Proof. exact (or_elim (@lem1237285 m n h2) (fun h0 : m = n => @lem1237510 A s m n h1 h0) (fun h0 : Peano.lt m n => @lem1237508 A s m n h1 h0)). Qed.
Lemma lem1237512 {A : Type'} (m : nat) (n : nat) (s : nat -> A) (h1 : term44 A n s) : term107 A n s m.
Proof. exact (fun h0 : term16 m n => @lem1237511 A s m n h1 h0). Qed.
Lemma lem1237517 {A : Type'} (n : nat) (s : nat -> A) (h1 : term44 A n s) : term110 A n s.
Proof. exact (fun m : nat => @lem1237512 A m n s h1). Qed.
Lemma lem1237518 {A : Type'} (n : nat) (s : nat -> A) (h1 : term44 A n s) : term58 A n s.
Proof. exact (EQ_MP (@lem1237284 A n s) (@lem1237517 A n s h1)). Qed.
Lemma lem1237519 {A : Type'} (n : nat) (s : nat -> A) : term60 A n s.
Proof. exact (fun h0 : term44 A n s => @lem1237518 A n s h0). Qed.
Lemma lem1237524 {A : Type'} (s : nat -> A) : term64 A s.
Proof. exact (fun n : nat => @lem1237519 A n s). Qed.
Lemma lem1237525 {A : Type'} (s : nat -> A) : term66 A s.
Proof. exact (conj (@lem1237221 A s) (@lem1237524 A s)). Qed.
Lemma lem1237526 {A : Type'} (s : nat -> A) : term47 A s.
Proof. exact (@lem1237182 A s (@lem1237525 A s)). Qed.
Lemma lem1237527 {A : Type'} (s : nat -> A) : term38 A s.
Proof. exact (EQ_MP (@lem1237159 A s) (@lem1237526 A s)). Qed.
Lemma lem1237532 {A : Type'} : term149 A.
Proof. exact (fun s : nat -> A => @lem1237527 A s). Qed.
