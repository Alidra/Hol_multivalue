Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247221_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import ADD_SYM_spec.
Require Import LE_ADDR_spec.
Require Import thm0_spec.
Require Import thm1246844_spec.
Require Import thm7_spec.
Lemma lem1247097 (m : nat) : term0 m.
Proof. exact (@lem100562 m). Qed.
Lemma lem1247098 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1247099 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1247098 m) (@lem1247097 m)). Qed.
Lemma lem1247100 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1247099 m n). Qed.
Lemma lem1247101 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1247102 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem1247101 m n) (@lem1247100 m n)). Qed.
Lemma lem1247103 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem1247105 (m : nat) : term4 m.
Proof. exact (@lem77960 m). Qed.
Lemma lem1247106 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem1247107 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem1247106 m) (@lem1247105 m)). Qed.
Lemma lem1247108 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem1247107 m n). Qed.
Lemma lem1247109 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem1247110 (m : nat) (n : nat) : term7 m n.
Proof. exact (EQ_MP (@lem1247109 m n) (@lem1247108 m n)). Qed.
Lemma lem1247111 (m : nat) (n : nat) (p : nat) : term8 m n p.
Proof. exact (@lem1247110 m n p). Qed.
Lemma lem1247112 (m : nat) (n : nat) (p : nat) : (term8 m n p) = ((term9 m n p) = (term10 m n p)).
Proof. exact (eq_refl (term8 m n p)). Qed.
Lemma lem1247114 (m : nat) : term11 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem1247115 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem1247116 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem1247115 m) (@lem1247114 m)). Qed.
Lemma lem1247117 (m : nat) (n : nat) : term13 m n.
Proof. exact (@lem1247116 m n). Qed.
Lemma lem1247118 (n : nat) (m : nat) : (term13 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term13 m n)). Qed.
Lemma lem1247120 (_22840 : nat) (_22841 : nat) (m : nat) (n : nat) : (term14 m n _22841 _22840) = (term15 _22840 _22841 m n).
Proof. exact (@lem1246844 _22840 _22841 (term16 m n)). Qed.
Lemma lem1247121 (m : nat) (n : nat) : (term17 m n) = (term18 m n).
Proof. exact (@lem1247120 n m m n). Qed.
Lemma lem1247122 (d : nat) (m : nat) (n : nat) : (term19 m n d) = (term20 d m n).
Proof. exact (eq_refl (term19 m n d)). Qed.
Lemma lem1247123 (n : nat) (m : nat) (d : nat) : (term21 n m d) = (term21 n m d).
Proof. exact (eq_refl (term21 n m d)). Qed.
Lemma lem1247124 (d : nat) (m : nat) (n : nat) : (term22 m n d) = (term23 d m n).
Proof. exact (MK_COMB (@lem1247123 n m d) (@lem1247122 d m n)). Qed.
Lemma lem1247125 (d : nat) (m : nat) (n : nat) : (term19 m n d) = (term20 d m n).
Proof. exact (eq_refl (term19 m n d)). Qed.
Lemma lem1247126 (m : nat) (n : nat) (d : nat) : (term21 m n d) = (term21 m n d).
Proof. exact (eq_refl (term21 m n d)). Qed.
Lemma lem1247127 (d : nat) (m : nat) (n : nat) : (term24 m n d) = (term25 d m n).
Proof. exact (MK_COMB (@lem1247126 m n d) (@lem1247125 d m n)). Qed.
Lemma lem1247128 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1247129 (d : nat) (m : nat) (n : nat) : (term26 m n d) = (term27 d m n).
Proof. exact (MK_COMB (@lem1247128) (@lem1247127 d m n)). Qed.
Lemma lem1247130 (d : nat) (m : nat) (n : nat) : (term28 m n d) = (term29 d m n).
Proof. exact (MK_COMB (@lem1247129 d m n) (@lem1247124 d m n)). Qed.
Lemma lem1247131 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (fun_ext (fun d : nat => @lem1247130 d m n)). Qed.
Lemma lem1247132 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1247133 (m : nat) (n : nat) : (term18 m n) = (term32 m n).
Proof. exact (MK_COMB (@lem1247132) (@lem1247131 m n)). Qed.
Lemma lem1247134 (m : nat) (n : nat) : (term17 m n) = (term33 m n).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem1247135 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247136 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (MK_COMB (@lem1247135) (@lem1247134 m n)). Qed.
Lemma lem1247137 (m : nat) (n : nat) : ((term17 m n) = (term18 m n)) = ((term33 m n) = (term32 m n)).
Proof. exact (MK_COMB (@lem1247136 m n) (@lem1247133 m n)). Qed.
Lemma lem1247138 (m : nat) (n : nat) : (term33 m n) = (term32 m n).
Proof. exact (EQ_MP (@lem1247137 m n) (@lem1247121 m n)). Qed.
Lemma lem1247139 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (SYM (@lem1247138 m n)). Qed.
Lemma lem1247140 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : m = (Nat.add n d).
Proof. exact (h1). Qed.
Lemma lem1247141 (d : nat) (n : nat) : (term36 d n) = (term36 d n).
Proof. exact (eq_refl (term36 d n)). Qed.
Lemma lem1247142 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term37 d n m) = (term38 n d).
Proof. exact (MK_COMB (@lem1247141 d n) (@lem1247140 m n d h1)). Qed.
Lemma lem1247143 (d : nat) (n : nat) : (term38 n d) = (term39 d n).
Proof. exact (eq_refl (term38 n d)). Qed.
Lemma lem1247144 (d : nat) (n : nat) (m : nat) : (term40 d n m) = (term40 d n m).
Proof. exact (eq_refl (term40 d n m)). Qed.
Lemma lem1247145 (m : nat) (d : nat) (n : nat) : ((term37 d n m) = (term38 n d)) = ((term37 d n m) = (term39 d n)).
Proof. exact (MK_COMB (@lem1247144 d n m) (@lem1247143 d n)). Qed.
Lemma lem1247146 (d : nat) (m : nat) (n : nat) : (term37 d n m) = (term20 d m n).
Proof. exact (eq_refl (term37 d n m)). Qed.
Lemma lem1247147 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247148 (d : nat) (m : nat) (n : nat) : (term40 d n m) = (term41 d m n).
Proof. exact (MK_COMB (@lem1247147) (@lem1247146 d m n)). Qed.
Lemma lem1247149 (d : nat) (n : nat) : (term39 d n) = (term39 d n).
Proof. exact (eq_refl (term39 d n)). Qed.
Lemma lem1247150 (m : nat) (d : nat) (n : nat) : ((term37 d n m) = (term39 d n)) = ((term20 d m n) = (term39 d n)).
Proof. exact (MK_COMB (@lem1247148 d m n) (@lem1247149 d n)). Qed.
Lemma lem1247151 (m : nat) (d : nat) (n : nat) : ((term37 d n m) = (term38 n d)) = ((term20 d m n) = (term39 d n)).
Proof. exact (TRANS (@lem1247145 m d n) (@lem1247150 m d n)). Qed.
Lemma lem1247152 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term20 d m n) = (term39 d n).
Proof. exact (EQ_MP (@lem1247151 m d n) (@lem1247142 m n d h1)). Qed.
Lemma lem1247153 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term39 d n) = (term20 d m n).
Proof. exact (SYM (@lem1247152 m n d h1)). Qed.
Lemma lem1247154 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : n = (Nat.add m d).
Proof. exact (h1). Qed.
Lemma lem1247155 (d : nat) (m : nat) : (term42 d m) = (term42 d m).
Proof. exact (eq_refl (term42 d m)). Qed.
Lemma lem1247156 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term43 d m n) = (term44 m d).
Proof. exact (MK_COMB (@lem1247155 d m) (@lem1247154 n m d h1)). Qed.
Lemma lem1247157 (m : nat) (d : nat) : (term44 m d) = (term45 m d).
Proof. exact (eq_refl (term44 m d)). Qed.
Lemma lem1247158 (d : nat) (m : nat) (n : nat) : (term46 d m n) = (term46 d m n).
Proof. exact (eq_refl (term46 d m n)). Qed.
Lemma lem1247159 (n : nat) (m : nat) (d : nat) : ((term43 d m n) = (term44 m d)) = ((term43 d m n) = (term45 m d)).
Proof. exact (MK_COMB (@lem1247158 d m n) (@lem1247157 m d)). Qed.
Lemma lem1247160 (d : nat) (m : nat) (n : nat) : (term43 d m n) = (term20 d m n).
Proof. exact (eq_refl (term43 d m n)). Qed.
Lemma lem1247161 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247162 (d : nat) (m : nat) (n : nat) : (term46 d m n) = (term41 d m n).
Proof. exact (MK_COMB (@lem1247161) (@lem1247160 d m n)). Qed.
Lemma lem1247163 (m : nat) (d : nat) : (term45 m d) = (term45 m d).
Proof. exact (eq_refl (term45 m d)). Qed.
Lemma lem1247164 (n : nat) (m : nat) (d : nat) : ((term43 d m n) = (term45 m d)) = ((term20 d m n) = (term45 m d)).
Proof. exact (MK_COMB (@lem1247162 d m n) (@lem1247163 m d)). Qed.
Lemma lem1247165 (n : nat) (m : nat) (d : nat) : ((term43 d m n) = (term44 m d)) = ((term20 d m n) = (term45 m d)).
Proof. exact (TRANS (@lem1247159 n m d) (@lem1247164 n m d)). Qed.
Lemma lem1247166 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term20 d m n) = (term45 m d).
Proof. exact (EQ_MP (@lem1247165 n m d) (@lem1247156 n m d h1)). Qed.
Lemma lem1247167 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term45 m d) = (term20 d m n).
Proof. exact (SYM (@lem1247166 n m d h1)). Qed.
Lemma lem1247169 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1247118 n m) (@lem1247117 m n)). Qed.
Lemma lem1247170 (n : nat) (d : nat) : (term47 d n) = (term48 n d).
Proof. exact (@lem1247169 n (Nat.add n d)). Qed.
Lemma lem1247171 (d : nat) : (Peano.le d) = (Peano.le d).
Proof. exact (eq_refl (Peano.le d)). Qed.
Lemma lem1247172 (n : nat) (d : nat) : (term39 d n) = (term45 n d).
Proof. exact (MK_COMB (@lem1247171 d) (@lem1247170 n d)). Qed.
Lemma lem1247173 (d : nat) (n : nat) : (term45 n d) = (term39 d n).
Proof. exact (SYM (@lem1247172 n d)). Qed.
Lemma lem1247177 (m : nat) (n : nat) (p : nat) : (term9 m n p) = (term10 m n p).
Proof. exact (EQ_MP (@lem1247112 m n p) (@lem1247111 m n p)). Qed.
Lemma lem1247178 (n : nat) (d : nat) : (term48 n d) = (term49 n d).
Proof. exact (@lem1247177 n n d). Qed.
Lemma lem1247179 (d : nat) : (Peano.le d) = (Peano.le d).
Proof. exact (eq_refl (Peano.le d)). Qed.
Lemma lem1247180 (n : nat) (d : nat) : (term45 n d) = (term50 n d).
Proof. exact (MK_COMB (@lem1247179 d) (@lem1247178 n d)). Qed.
Lemma lem1247182 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem1247103 m n) (@lem1247102 m n)). Qed.
Lemma lem1247183 (n : nat) (d : nat) : (term50 n d) = True.
Proof. exact (@lem1247182 (Nat.add n n) d). Qed.
Lemma lem1247184 (n : nat) (d : nat) : (term45 n d) = True.
Proof. exact (TRANS (@lem1247180 n d) (@lem1247183 n d)). Qed.
Lemma lem1247185 (n : nat) (d : nat) : True = (term45 n d).
Proof. exact (SYM (@lem1247184 n d)). Qed.
Lemma lem1247186 (n : nat) (d : nat) : term45 n d.
Proof. exact (EQ_MP (@lem1247185 n d) (@lem0)). Qed.
Lemma lem1247190 (m : nat) (n : nat) (p : nat) : (term9 m n p) = (term10 m n p).
Proof. exact (EQ_MP (@lem1247112 m n p) (@lem1247111 m n p)). Qed.
Lemma lem1247191 (m : nat) (d : nat) : (term48 m d) = (term49 m d).
Proof. exact (@lem1247190 m m d). Qed.
Lemma lem1247192 (d : nat) : (Peano.le d) = (Peano.le d).
Proof. exact (eq_refl (Peano.le d)). Qed.
Lemma lem1247193 (m : nat) (d : nat) : (term45 m d) = (term50 m d).
Proof. exact (MK_COMB (@lem1247192 d) (@lem1247191 m d)). Qed.
Lemma lem1247195 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem1247103 m n) (@lem1247102 m n)). Qed.
Lemma lem1247196 (m : nat) (d : nat) : (term50 m d) = True.
Proof. exact (@lem1247195 (Nat.add m m) d). Qed.
Lemma lem1247197 (m : nat) (d : nat) : (term45 m d) = True.
Proof. exact (TRANS (@lem1247193 m d) (@lem1247196 m d)). Qed.
Lemma lem1247198 (m : nat) (d : nat) : True = (term45 m d).
Proof. exact (SYM (@lem1247197 m d)). Qed.
Lemma lem1247199 (m : nat) (d : nat) : term45 m d.
Proof. exact (EQ_MP (@lem1247198 m d) (@lem0)). Qed.
Lemma lem1247200 (d : nat) (n : nat) : term39 d n.
Proof. exact (EQ_MP (@lem1247173 d n) (@lem1247186 n d)). Qed.
Lemma lem1247201 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : term20 d m n.
Proof. exact (EQ_MP (@lem1247167 n m d h1) (@lem1247199 m d)). Qed.
Lemma lem1247202 (d : nat) (m : nat) (n : nat) : term23 d m n.
Proof. exact (fun h0 : n = (Nat.add m d) => @lem1247201 n m d h0). Qed.
Lemma lem1247203 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : term20 d m n.
Proof. exact (EQ_MP (@lem1247153 m n d h1) (@lem1247200 d n)). Qed.
Lemma lem1247204 (d : nat) (m : nat) (n : nat) : term25 d m n.
Proof. exact (fun h0 : m = (Nat.add n d) => @lem1247203 m n d h0). Qed.
Lemma lem1247205 (d : nat) (m : nat) (n : nat) : term29 d m n.
Proof. exact (conj (@lem1247204 d m n) (@lem1247202 d m n)). Qed.
Lemma lem1247210 (m : nat) (n : nat) : term32 m n.
Proof. exact (fun d : nat => @lem1247205 d m n). Qed.
Lemma lem1247211 (m : nat) (n : nat) : term33 m n.
Proof. exact (EQ_MP (@lem1247139 m n) (@lem1247210 m n)). Qed.
Lemma lem1247216 (m : nat) : term51 m.
Proof. exact (fun n : nat => @lem1247211 m n). Qed.
Lemma lem1247221 : term52.
Proof. exact (fun m : nat => @lem1247216 m). Qed.
