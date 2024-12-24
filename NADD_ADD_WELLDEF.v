Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_ADD_WELLDEF_term_abbrevs.
Require Import LE_ADD2_spec.
Require Import NADD_ADD_spec.
Require Import nadd_eq_spec.
Require Import thm0_spec.
Require Import thm1259721_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1842_spec.
Require Import thm272809_spec.
Require Import thm7_spec.
Lemma lem1274105 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1274106 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem1274105 h1 m). Qed.
Lemma lem1274107 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1274108 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem1274107 m) (@lem1274106 m h1)). Qed.
Lemma lem1274109 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem1274108 m h1 n). Qed.
Lemma lem1274110 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1274111 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (EQ_MP (@lem1274110 m n) (@lem1274109 m n h1)). Qed.
Lemma lem1274112 (m : nat) (n : nat) (p : nat) (h1 : term0) : term5 m n p.
Proof. exact (@lem1274111 m n h1 p). Qed.
Lemma lem1274113 (m : nat) (n : nat) (p : nat) : (term5 m n p) = (term6 m n p).
Proof. exact (eq_refl (term5 m n p)). Qed.
Lemma lem1274114 (m : nat) (n : nat) (p : nat) (h1 : term0) : term6 m n p.
Proof. exact (EQ_MP (@lem1274113 m n p) (@lem1274112 m n p h1)). Qed.
Lemma lem1274115 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term0) : term7 m n p q.
Proof. exact (@lem1274114 m n p h1 q). Qed.
Lemma lem1274116 (m : nat) (n : nat) (p : nat) (q : nat) : (term7 m n p q) = (term8 m n p q).
Proof. exact (eq_refl (term7 m n p q)). Qed.
Lemma lem1274117 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term0) : term8 m n p q.
Proof. exact (EQ_MP (@lem1274116 m n p q) (@lem1274115 m n p q h1)). Qed.
Lemma lem1274118 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term9 m p n q) : term9 m p n q.
Proof. exact (h1). Qed.
Lemma lem1274119 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term0) (h2 : term9 m p n q) : term10 m n p q.
Proof. exact (@lem1274117 m n p q h1 (@lem1274118 m p n q h2)). Qed.
Lemma lem1274120 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term9 m p n q) : term11 m n p q.
Proof. exact (fun h0 : term0 => @lem1274119 m p n q h0 h1). Qed.
Lemma lem1274121 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1274122 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term0) (h2 : term9 m p n q) : term10 m n p q.
Proof. exact (@lem1274120 m p n q h2 (@lem1274121 h1)). Qed.
Lemma lem1274123 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term0) : term8 m n p q.
Proof. exact (fun h0 : term9 m p n q => @lem1274122 m p n q h1 h0). Qed.
Lemma lem1274124 (m : nat) (n : nat) (p : nat) (h1 : term0) : term6 m n p.
Proof. exact (fun q : nat => @lem1274123 m n p q h1). Qed.
Lemma lem1274125 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (fun p : nat => @lem1274124 m n p h1). Qed.
Lemma lem1274126 (m : nat) (h1 : term0) : term2 m.
Proof. exact (fun n : nat => @lem1274125 m n h1). Qed.
Lemma lem1274127 (h1 : term0) : term0.
Proof. exact (fun m : nat => @lem1274126 m h1). Qed.
Lemma lem1274128 : term12.
Proof. exact (fun h0 : term0 => @lem1274127 h0). Qed.
Lemma lem1274129 : term0.
Proof. exact (@lem1274128 (@lem101399)). Qed.
Lemma lem1274130 (m : nat) : term1 m.
Proof. exact (@lem1274129 m). Qed.
Lemma lem1274131 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1274132 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem1274131 m) (@lem1274130 m)). Qed.
Lemma lem1274133 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem1274132 m n). Qed.
Lemma lem1274134 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1274135 (m : nat) (n : nat) : term4 m n.
Proof. exact (EQ_MP (@lem1274134 m n) (@lem1274133 m n)). Qed.
Lemma lem1274136 (m : nat) (n : nat) (p : nat) : term5 m n p.
Proof. exact (@lem1274135 m n p). Qed.
Lemma lem1274137 (m : nat) (n : nat) (p : nat) : (term5 m n p) = (term6 m n p).
Proof. exact (eq_refl (term5 m n p)). Qed.
Lemma lem1274138 (m : nat) (n : nat) (p : nat) : term6 m n p.
Proof. exact (EQ_MP (@lem1274137 m n p) (@lem1274136 m n p)). Qed.
Lemma lem1274139 (m : nat) (n : nat) (p : nat) (q : nat) : term7 m n p q.
Proof. exact (@lem1274138 m n p q). Qed.
Lemma lem1274140 (m : nat) (n : nat) (p : nat) (q : nat) : (term7 m n p q) = (term8 m n p q).
Proof. exact (eq_refl (term7 m n p q)). Qed.
Lemma lem1274142 (m : nat) : term13 m.
Proof. exact (@lem1259721 m). Qed.
Lemma lem1274143 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem1274144 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem1274143 m) (@lem1274142 m)). Qed.
Lemma lem1274145 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem1274144 m n). Qed.
Lemma lem1274146 (m : nat) (n : nat) : (term15 m n) = (term16 m n).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem1274147 (m : nat) (n : nat) : term16 m n.
Proof. exact (EQ_MP (@lem1274146 m n) (@lem1274145 m n)). Qed.
Lemma lem1274148 (m : nat) (n : nat) (p : nat) : term17 m n p.
Proof. exact (@lem1274147 m n p). Qed.
Lemma lem1274149 (m : nat) (p : nat) (n : nat) : (term17 m n p) = (term18 m p n).
Proof. exact (eq_refl (term17 m n p)). Qed.
Lemma lem1274150 (m : nat) (p : nat) (n : nat) : term18 m p n.
Proof. exact (EQ_MP (@lem1274149 m p n) (@lem1274148 m n p)). Qed.
Lemma lem1274151 (m : nat) (p : nat) (n : nat) (q : nat) : term19 m p n q.
Proof. exact (@lem1274150 m p n q). Qed.
Lemma lem1274152 (m : nat) (p : nat) (n : nat) (q : nat) : (term19 m p n q) = (term20 m p n q).
Proof. exact (eq_refl (term19 m p n q)). Qed.
Lemma lem1274153 (m : nat) (p : nat) (n : nat) (q : nat) : term20 m p n q.
Proof. exact (EQ_MP (@lem1274152 m p n q) (@lem1274151 m p n q)). Qed.
Lemma lem1274154 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem1274155 (m : nat) (h1 : term21) : term22 m.
Proof. exact (@lem1274154 h1 m). Qed.
Lemma lem1274156 (m : nat) : (term22 m) = (term23 m).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem1274157 (m : nat) (h1 : term21) : term23 m.
Proof. exact (EQ_MP (@lem1274156 m) (@lem1274155 m h1)). Qed.
Lemma lem1274158 (m : nat) (n : nat) (h1 : term21) : term24 m n.
Proof. exact (@lem1274157 m h1 n). Qed.
Lemma lem1274159 (n : nat) (m : nat) : (term24 m n) = (term25 n m).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem1274160 (n : nat) (m : nat) (h1 : term21) : term25 n m.
Proof. exact (EQ_MP (@lem1274159 n m) (@lem1274158 m n h1)). Qed.
Lemma lem1274161 (n : nat) (m : nat) (p : nat) (h1 : term21) : term26 n m p.
Proof. exact (@lem1274160 n m h1 p). Qed.
Lemma lem1274162 (n : nat) (m : nat) (p : nat) : (term26 n m p) = (term27 n m p).
Proof. exact (eq_refl (term26 n m p)). Qed.
Lemma lem1274163 (n : nat) (m : nat) (p : nat) (h1 : term21) : term27 n m p.
Proof. exact (EQ_MP (@lem1274162 n m p) (@lem1274161 n m p h1)). Qed.
Lemma lem1274164 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1274165 (p : nat) (m : nat) (n : nat) (h1 : term21) (h2 : Peano.le m n) : term28 n m p.
Proof. exact (@lem1274163 n m p h1 (@lem1274164 m n h2)). Qed.
Lemma lem1274166 (m : nat) (n : nat) (h1 : term21) (h2 : Peano.le m n) : term29 n m.
Proof. exact (fun p : nat => @lem1274165 p m n h1 h2). Qed.
Lemma lem1274167 (n : nat) (m : nat) (h1 : term21) : term30 n m.
Proof. exact (fun h0 : Peano.le m n => @lem1274166 m n h1 h0). Qed.
Lemma lem1274168 (m : nat) (h1 : term21) : term31 m.
Proof. exact (fun n : nat => @lem1274167 n m h1). Qed.
Lemma lem1274169 (h1 : term21) : term32.
Proof. exact (fun m : nat => @lem1274168 m h1). Qed.
Lemma lem1274170 : term33.
Proof. exact (fun h0 : term21 => @lem1274169 h0). Qed.
Lemma lem1274171 : term32.
Proof. exact (@lem1274170 (@lem272809)). Qed.
Lemma lem1274172 (m : nat) : term34 m.
Proof. exact (@lem1274171 m). Qed.
Lemma lem1274173 (m : nat) : (term34 m) = (term31 m).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem1274174 (m : nat) : term31 m.
Proof. exact (EQ_MP (@lem1274173 m) (@lem1274172 m)). Qed.
Lemma lem1274175 (m : nat) (n : nat) : term35 m n.
Proof. exact (@lem1274174 m n). Qed.
Lemma lem1274176 (n : nat) (m : nat) : (term35 m n) = (term30 n m).
Proof. exact (eq_refl (term35 m n)). Qed.
Lemma lem1274179 (n : nat) (m : nat) : term30 n m.
Proof. exact (EQ_MP (@lem1274176 n m) (@lem1274175 m n)). Qed.
Lemma lem1274180 (m : nat) (n : nat) (p : nat) (q : nat) : term36 m n p q.
Proof. exact (@lem1274179 (term37 m p n q) (term38 m n p q)). Qed.
Lemma lem1274181 (m : nat) (n : nat) (p : nat) (q : nat) : term39 m n p q.
Proof. exact (@lem1274180 m n p q (@lem1274153 m p n q)). Qed.
Lemma lem1274182 (m : nat) (n : nat) (p : nat) : term40 m n p.
Proof. exact (fun q : nat => @lem1274181 m n p q). Qed.
Lemma lem1274183 (m : nat) (n : nat) : term41 m n.
Proof. exact (fun p : nat => @lem1274182 m n p). Qed.
Lemma lem1274184 (m : nat) : term42 m.
Proof. exact (fun n : nat => @lem1274183 m n). Qed.
Lemma lem1274185 : term43.
Proof. exact (fun m : nat => @lem1274184 m). Qed.
Lemma lem1274186 (h1 : term43) : term43.
Proof. exact (h1). Qed.
Lemma lem1274187 (m : nat) (h1 : term43) : term44 m.
Proof. exact (@lem1274186 h1 m). Qed.
Lemma lem1274188 (m : nat) : (term44 m) = (term42 m).
Proof. exact (eq_refl (term44 m)). Qed.
Lemma lem1274189 (m : nat) (h1 : term43) : term42 m.
Proof. exact (EQ_MP (@lem1274188 m) (@lem1274187 m h1)). Qed.
Lemma lem1274190 (m : nat) (n : nat) (h1 : term43) : term45 m n.
Proof. exact (@lem1274189 m h1 n). Qed.
Lemma lem1274191 (m : nat) (n : nat) : (term45 m n) = (term41 m n).
Proof. exact (eq_refl (term45 m n)). Qed.
Lemma lem1274192 (m : nat) (n : nat) (h1 : term43) : term41 m n.
Proof. exact (EQ_MP (@lem1274191 m n) (@lem1274190 m n h1)). Qed.
Lemma lem1274193 (m : nat) (n : nat) (p : nat) (h1 : term43) : term46 m n p.
Proof. exact (@lem1274192 m n h1 p). Qed.
Lemma lem1274194 (m : nat) (n : nat) (p : nat) : (term46 m n p) = (term40 m n p).
Proof. exact (eq_refl (term46 m n p)). Qed.
Lemma lem1274195 (m : nat) (n : nat) (p : nat) (h1 : term43) : term40 m n p.
Proof. exact (EQ_MP (@lem1274194 m n p) (@lem1274193 m n p h1)). Qed.
Lemma lem1274196 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term43) : term47 m n p q.
Proof. exact (@lem1274195 m n p h1 q). Qed.
Lemma lem1274197 (m : nat) (n : nat) (p : nat) (q : nat) : (term47 m n p q) = (term39 m n p q).
Proof. exact (eq_refl (term47 m n p q)). Qed.
Lemma lem1274198 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term43) : term39 m n p q.
Proof. exact (EQ_MP (@lem1274197 m n p q) (@lem1274196 m n p q h1)). Qed.
Lemma lem1274199 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) (h1 : term43) : term48 m n p q p'.
Proof. exact (@lem1274198 m n p q h1 p'). Qed.
Lemma lem1274200 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) : (term48 m n p q p') = (term49 m n p q p').
Proof. exact (eq_refl (term48 m n p q p')). Qed.
Lemma lem1274201 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) (h1 : term43) : term49 m n p q p'.
Proof. exact (EQ_MP (@lem1274200 m n p q p') (@lem1274199 m n p q p' h1)). Qed.
Lemma lem1274202 (m : nat) (p : nat) (n : nat) (q : nat) (p' : nat) (h1 : term50 m p n q p') : term50 m p n q p'.
Proof. exact (h1). Qed.
Lemma lem1274203 (m : nat) (p : nat) (n : nat) (q : nat) (p' : nat) (h1 : term43) (h2 : term50 m p n q p') : term51 m n p q p'.
Proof. exact (@lem1274201 m n p q p' h1 (@lem1274202 m p n q p' h2)). Qed.
Lemma lem1274204 (m : nat) (p : nat) (n : nat) (q : nat) (p' : nat) (h1 : term50 m p n q p') : term52 m n p q p'.
Proof. exact (fun h0 : term43 => @lem1274203 m p n q p' h0 h1). Qed.
Lemma lem1274205 (h1 : term43) : term43.
Proof. exact (h1). Qed.
Lemma lem1274206 (m : nat) (p : nat) (n : nat) (q : nat) (p' : nat) (h1 : term43) (h2 : term50 m p n q p') : term51 m n p q p'.
Proof. exact (@lem1274204 m p n q p' h2 (@lem1274205 h1)). Qed.
Lemma lem1274207 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) (h1 : term43) : term49 m n p q p'.
Proof. exact (fun h0 : term50 m p n q p' => @lem1274206 m p n q p' h1 h0). Qed.
Lemma lem1274208 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term43) : term39 m n p q.
Proof. exact (fun p' : nat => @lem1274207 m n p q p' h1). Qed.
Lemma lem1274209 (m : nat) (n : nat) (p : nat) (h1 : term43) : term40 m n p.
Proof. exact (fun q : nat => @lem1274208 m n p q h1). Qed.
Lemma lem1274210 (m : nat) (n : nat) (h1 : term43) : term41 m n.
Proof. exact (fun p : nat => @lem1274209 m n p h1). Qed.
Lemma lem1274211 (m : nat) (h1 : term43) : term42 m.
Proof. exact (fun n : nat => @lem1274210 m n h1). Qed.
Lemma lem1274212 (h1 : term43) : term43.
Proof. exact (fun m : nat => @lem1274211 m h1). Qed.
Lemma lem1274213 : term53.
Proof. exact (fun h0 : term43 => @lem1274212 h0). Qed.
Lemma lem1274214 : term43.
Proof. exact (@lem1274213 (@lem1274185)). Qed.
Lemma lem1274215 (m : nat) : term44 m.
Proof. exact (@lem1274214 m). Qed.
Lemma lem1274216 (m : nat) : (term44 m) = (term42 m).
Proof. exact (eq_refl (term44 m)). Qed.
Lemma lem1274217 (m : nat) : term42 m.
Proof. exact (EQ_MP (@lem1274216 m) (@lem1274215 m)). Qed.
Lemma lem1274218 (m : nat) (n : nat) : term45 m n.
Proof. exact (@lem1274217 m n). Qed.
Lemma lem1274219 (m : nat) (n : nat) : (term45 m n) = (term41 m n).
Proof. exact (eq_refl (term45 m n)). Qed.
Lemma lem1274220 (m : nat) (n : nat) : term41 m n.
Proof. exact (EQ_MP (@lem1274219 m n) (@lem1274218 m n)). Qed.
Lemma lem1274221 (m : nat) (n : nat) (p : nat) : term46 m n p.
Proof. exact (@lem1274220 m n p). Qed.
Lemma lem1274222 (m : nat) (n : nat) (p : nat) : (term46 m n p) = (term40 m n p).
Proof. exact (eq_refl (term46 m n p)). Qed.
Lemma lem1274223 (m : nat) (n : nat) (p : nat) : term40 m n p.
Proof. exact (EQ_MP (@lem1274222 m n p) (@lem1274221 m n p)). Qed.
Lemma lem1274224 (m : nat) (n : nat) (p : nat) (q : nat) : term47 m n p q.
Proof. exact (@lem1274223 m n p q). Qed.
Lemma lem1274225 (m : nat) (n : nat) (p : nat) (q : nat) : (term47 m n p q) = (term39 m n p q).
Proof. exact (eq_refl (term47 m n p q)). Qed.
Lemma lem1274226 (m : nat) (n : nat) (p : nat) (q : nat) : term39 m n p q.
Proof. exact (EQ_MP (@lem1274225 m n p q) (@lem1274224 m n p q)). Qed.
Lemma lem1274227 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) : term48 m n p q p'.
Proof. exact (@lem1274226 m n p q p'). Qed.
Lemma lem1274228 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) : (term48 m n p q p') = (term49 m n p q p').
Proof. exact (eq_refl (term48 m n p q p')). Qed.
Lemma lem1274230 (x : nadd) : term54 x.
Proof. exact (@lem1274104 x). Qed.
Lemma lem1274231 (x : nadd) : (term54 x) = (term55 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1274232 (x : nadd) : term55 x.
Proof. exact (EQ_MP (@lem1274231 x) (@lem1274230 x)). Qed.
Lemma lem1274233 (x : nadd) (y : nadd) : term56 x y.
Proof. exact (@lem1274232 x y). Qed.
Lemma lem1274234 (x : nadd) (y : nadd) : (term56 x y) = ((term57 x y) = (term58 x y)).
Proof. exact (eq_refl (term56 x y)). Qed.
Lemma lem1274236 (x : nadd) : term59 x.
Proof. exact (@lem1267930 x). Qed.
Lemma lem1274237 (x : nadd) : (term59 x) = (term60 x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem1274238 (x : nadd) : term60 x.
Proof. exact (EQ_MP (@lem1274237 x) (@lem1274236 x)). Qed.
Lemma lem1274239 (x : nadd) (y : nadd) : term61 x y.
Proof. exact (@lem1274238 x y). Qed.
Lemma lem1274240 (x : nadd) (y : nadd) : (term61 x y) = ((nadd_eq x y) = (term62 x y)).
Proof. exact (eq_refl (term61 x y)). Qed.
Lemma lem1274247 (x : nadd) (y : nadd) : (nadd_eq x y) = (term62 x y).
Proof. exact (EQ_MP (@lem1274240 x y) (@lem1274239 x y)). Qed.
Lemma lem1274248 (x : nadd) (x' : nadd) : (nadd_eq x x') = (term62 x x').
Proof. exact (@lem1274247 x x'). Qed.
Lemma lem1274257 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1274258 (x : nadd) (x' : nadd) : (term63 x x') = (term64 x x').
Proof. exact (MK_COMB (@lem1274257) (@lem1274248 x x')). Qed.
Lemma lem1274260 (x : nadd) (y : nadd) : (nadd_eq x y) = (term62 x y).
Proof. exact (EQ_MP (@lem1274240 x y) (@lem1274239 x y)). Qed.
Lemma lem1274261 (y : nadd) (y' : nadd) : (nadd_eq y y') = (term62 y y').
Proof. exact (@lem1274260 y y'). Qed.
Lemma lem1274270 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term65 x x' y y') = (term66 x x' y y').
Proof. exact (MK_COMB (@lem1274258 x x') (@lem1274261 y y')). Qed.
Lemma lem1274273 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1274274 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term67 x x' y y') = (term68 x x' y y').
Proof. exact (MK_COMB (@lem1274273) (@lem1274270 x x' y y')). Qed.
Lemma lem1274276 (x : nadd) (y : nadd) : (nadd_eq x y) = (term62 x y).
Proof. exact (EQ_MP (@lem1274240 x y) (@lem1274239 x y)). Qed.
Lemma lem1274277 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term69 x y x' y') = (term70 x y x' y').
Proof. exact (@lem1274276 (nadd_add x y) (nadd_add x' y')). Qed.
Lemma lem1274287 (x : nadd) (y : nadd) : (term57 x y) = (term58 x y).
Proof. exact (EQ_MP (@lem1274234 x y) (@lem1274233 x y)). Qed.
Lemma lem1274288 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1274289 (x : nadd) (y : nadd) (n : nat) : (term71 x y n) = (term72 x y n).
Proof. exact (MK_COMB (@lem1274287 x y) (@lem1274288 n)). Qed.
Lemma lem1274291 {A B : Type'} (f : A -> B) (y : A) : (term73 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1274292 (f : nat -> nat) (y : nat) : (term74 f y) = (f y).
Proof. exact (@lem1274291 nat nat f y). Qed.
Lemma lem1274293 (x : nadd) (y : nadd) (n : nat) : (term75 x y n) = (term72 x y n).
Proof. exact (@lem1274292 (term58 x y) n). Qed.
Lemma lem1274294 (x : nadd) (y : nadd) (n : nat) : (term72 x y n) = (term76 x y n).
Proof. exact (eq_refl (term72 x y n)). Qed.
Lemma lem1274295 (x : nadd) (y : nadd) : (term77 x y) = (term58 x y).
Proof. exact (fun_ext (fun n : nat => @lem1274294 x y n)). Qed.
Lemma lem1274296 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1274297 (x : nadd) (y : nadd) (n : nat) : (term75 x y n) = (term72 x y n).
Proof. exact (MK_COMB (@lem1274295 x y) (@lem1274296 n)). Qed.
Lemma lem1274298 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1274299 (x : nadd) (y : nadd) (n : nat) : (term78 x y n) = (term79 x y n).
Proof. exact (MK_COMB (@lem1274298) (@lem1274297 x y n)). Qed.
Lemma lem1274300 (x : nadd) (y : nadd) (n : nat) : (term72 x y n) = (term76 x y n).
Proof. exact (eq_refl (term72 x y n)). Qed.
Lemma lem1274301 (x : nadd) (y : nadd) (n : nat) : ((term75 x y n) = (term72 x y n)) = ((term72 x y n) = (term76 x y n)).
Proof. exact (MK_COMB (@lem1274299 x y n) (@lem1274300 x y n)). Qed.
Lemma lem1274302 (x : nadd) (y : nadd) (n : nat) : (term72 x y n) = (term76 x y n).
Proof. exact (EQ_MP (@lem1274301 x y n) (@lem1274293 x y n)). Qed.
Lemma lem1274303 (x : nadd) (y : nadd) (n : nat) : (term71 x y n) = (term76 x y n).
Proof. exact (TRANS (@lem1274289 x y n) (@lem1274302 x y n)). Qed.
Lemma lem1274304 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1274305 (x : nadd) (y : nadd) (n : nat) : (term80 x y n) = (term81 x y n).
Proof. exact (MK_COMB (@lem1274304) (@lem1274303 x y n)). Qed.
Lemma lem1274307 (x : nadd) (y : nadd) : (term57 x y) = (term58 x y).
Proof. exact (EQ_MP (@lem1274234 x y) (@lem1274233 x y)). Qed.
Lemma lem1274308 (x' : nadd) (y' : nadd) : (term57 x' y') = (term58 x' y').
Proof. exact (@lem1274307 x' y'). Qed.
Lemma lem1274309 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1274310 (x' : nadd) (y' : nadd) (n : nat) : (term71 x' y' n) = (term72 x' y' n).
Proof. exact (MK_COMB (@lem1274308 x' y') (@lem1274309 n)). Qed.
Lemma lem1274312 {A B : Type'} (f : A -> B) (y : A) : (term73 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1274313 (f : nat -> nat) (y : nat) : (term74 f y) = (f y).
Proof. exact (@lem1274312 nat nat f y). Qed.
Lemma lem1274314 (x' : nadd) (y' : nadd) (n : nat) : (term75 x' y' n) = (term72 x' y' n).
Proof. exact (@lem1274313 (term58 x' y') n). Qed.
Lemma lem1274315 (x' : nadd) (y' : nadd) (n : nat) : (term72 x' y' n) = (term76 x' y' n).
Proof. exact (eq_refl (term72 x' y' n)). Qed.
Lemma lem1274316 (x' : nadd) (y' : nadd) : (term77 x' y') = (term58 x' y').
Proof. exact (fun_ext (fun n : nat => @lem1274315 x' y' n)). Qed.
Lemma lem1274317 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1274318 (x' : nadd) (y' : nadd) (n : nat) : (term75 x' y' n) = (term72 x' y' n).
Proof. exact (MK_COMB (@lem1274316 x' y') (@lem1274317 n)). Qed.
Lemma lem1274319 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1274320 (x' : nadd) (y' : nadd) (n : nat) : (term78 x' y' n) = (term79 x' y' n).
Proof. exact (MK_COMB (@lem1274319) (@lem1274318 x' y' n)). Qed.
Lemma lem1274321 (x' : nadd) (y' : nadd) (n : nat) : (term72 x' y' n) = (term76 x' y' n).
Proof. exact (eq_refl (term72 x' y' n)). Qed.
Lemma lem1274322 (x' : nadd) (y' : nadd) (n : nat) : ((term75 x' y' n) = (term72 x' y' n)) = ((term72 x' y' n) = (term76 x' y' n)).
Proof. exact (MK_COMB (@lem1274320 x' y' n) (@lem1274321 x' y' n)). Qed.
Lemma lem1274323 (x' : nadd) (y' : nadd) (n : nat) : (term72 x' y' n) = (term76 x' y' n).
Proof. exact (EQ_MP (@lem1274322 x' y' n) (@lem1274314 x' y' n)). Qed.
Lemma lem1274324 (x' : nadd) (y' : nadd) (n : nat) : (term71 x' y' n) = (term76 x' y' n).
Proof. exact (TRANS (@lem1274310 x' y' n) (@lem1274323 x' y' n)). Qed.
Lemma lem1274325 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (n : nat) : (term82 x y x' y' n) = (term83 x y x' y' n).
Proof. exact (MK_COMB (@lem1274305 x y n) (@lem1274324 x' y' n)). Qed.
Lemma lem1274326 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1274327 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (n : nat) : (term84 x y x' y' n) = (term85 x y x' y' n).
Proof. exact (MK_COMB (@lem1274326) (@lem1274325 x y x' y' n)). Qed.
Lemma lem1274328 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1274329 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (n : nat) : (term86 x y x' y' n) = (term87 x y x' y' n).
Proof. exact (MK_COMB (@lem1274328) (@lem1274327 x y x' y' n)). Qed.
Lemma lem1274330 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1274331 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (n : nat) (B : nat) : (term88 x y x' y' n B) = (term89 x y x' y' n B).
Proof. exact (MK_COMB (@lem1274329 x y x' y' n) (@lem1274330 B)). Qed.
Lemma lem1274332 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (B : nat) : (term90 x y x' y' B) = (term91 x y x' y' B).
Proof. exact (fun_ext (fun n : nat => @lem1274331 x y x' y' n B)). Qed.
Lemma lem1274333 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1274334 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (B : nat) : (term92 x y x' y' B) = (term93 x y x' y' B).
Proof. exact (MK_COMB (@lem1274333) (@lem1274332 x y x' y' B)). Qed.
Lemma lem1274339 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term94 x y x' y') = (term95 x y x' y').
Proof. exact (fun_ext (fun B : nat => @lem1274334 x y x' y' B)). Qed.
Lemma lem1274340 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1274341 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term70 x y x' y') = (term96 x y x' y').
Proof. exact (MK_COMB (@lem1274340) (@lem1274339 x y x' y')). Qed.
Lemma lem1274346 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term69 x y x' y') = (term96 x y x' y').
Proof. exact (TRANS (@lem1274277 x y x' y') (@lem1274341 x y x' y')). Qed.
Lemma lem1274347 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term97 x y x' y') = (term98 x y x' y').
Proof. exact (MK_COMB (@lem1274274 x x' y y') (@lem1274346 x y x' y')). Qed.
Lemma lem1274350 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term98 x y x' y') = (term97 x y x' y').
Proof. exact (SYM (@lem1274347 x y x' y')). Qed.
Lemma lem1274351 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term66 x x' y y') : term66 x x' y y'.
Proof. exact (h1). Qed.
Lemma lem1274352 (y : nadd) (y' : nadd) (h1 : term62 y y') : term62 y y'.
Proof. exact (h1). Qed.
Lemma lem1274353 (y : nadd) (y' : nadd) (B2 : nat) (h1 : term99 y y' B2) : term99 y y' B2.
Proof. exact (h1). Qed.
Lemma lem1274354 (x : nadd) (x' : nadd) (h1 : term62 x x') : term62 x x'.
Proof. exact (h1). Qed.
Lemma lem1274355 (x : nadd) (x' : nadd) (B1 : nat) (h1 : term99 x x' B1) : term99 x x' B1.
Proof. exact (h1). Qed.
Lemma lem1274357 (m : nat) (n : nat) (p : nat) (q : nat) (p' : nat) : term49 m n p q p'.
Proof. exact (EQ_MP (@lem1274228 m n p q p') (@lem1274227 m n p q p')). Qed.
Lemma lem1274358 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (n : nat) (B1 : nat) (B2 : nat) : term100 x y x' y' n B1 B2.
Proof. exact (@lem1274357 (dest_nadd x n) (dest_nadd y n) (dest_nadd x' n) (dest_nadd y' n) (Nat.add B1 B2)). Qed.
Lemma lem1274360 (m : nat) (n : nat) (p : nat) (q : nat) : term8 m n p q.
Proof. exact (EQ_MP (@lem1274140 m n p q) (@lem1274139 m n p q)). Qed.
Lemma lem1274361 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (n : nat) (B1 : nat) (B2 : nat) : term101 x x' y y' n B1 B2.
Proof. exact (@lem1274360 (term102 x x' n) (term102 y y' n) B1 B2). Qed.
Lemma lem1274362 (n : nat) (x : nadd) (x' : nadd) (B1 : nat) (h1 : term99 x x' B1) : term103 x x' B1 n.
Proof. exact (@lem1274355 x x' B1 h1 n). Qed.
Lemma lem1274363 (x : nadd) (x' : nadd) (n : nat) (B1 : nat) : (term103 x x' B1 n) = (term104 x x' n B1).
Proof. exact (eq_refl (term103 x x' B1 n)). Qed.
Lemma lem1274364 (n : nat) (x : nadd) (x' : nadd) (B1 : nat) (h1 : term99 x x' B1) : term104 x x' n B1.
Proof. exact (EQ_MP (@lem1274363 x x' n B1) (@lem1274362 n x x' B1 h1)). Qed.
Lemma lem1274365 (x : nadd) (x' : nadd) (n : nat) (B1 : nat) : (term104 x x' n B1) = ((term104 x x' n B1) = True).
Proof. exact (@lem7 (term104 x x' n B1)). Qed.
Lemma lem1274367 (n : nat) (y : nadd) (y' : nadd) (B2 : nat) (h1 : term99 y y' B2) : term103 y y' B2 n.
Proof. exact (@lem1274353 y y' B2 h1 n). Qed.
Lemma lem1274368 (y : nadd) (y' : nadd) (n : nat) (B2 : nat) : (term103 y y' B2 n) = (term104 y y' n B2).
Proof. exact (eq_refl (term103 y y' B2 n)). Qed.
Lemma lem1274369 (n : nat) (y : nadd) (y' : nadd) (B2 : nat) (h1 : term99 y y' B2) : term104 y y' n B2.
Proof. exact (EQ_MP (@lem1274368 y y' n B2) (@lem1274367 n y y' B2 h1)). Qed.
Lemma lem1274370 (y : nadd) (y' : nadd) (n : nat) (B2 : nat) : (term104 y y' n B2) = ((term104 y y' n B2) = True).
Proof. exact (@lem7 (term104 y y' n B2)). Qed.
Lemma lem1274375 (n : nat) (x : nadd) (x' : nadd) (B1 : nat) (h1 : term99 x x' B1) : (term104 x x' n B1) = True.
Proof. exact (EQ_MP (@lem1274365 x x' n B1) (@lem1274364 n x x' B1 h1)). Qed.
Lemma lem1274376 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1274377 (n : nat) (x : nadd) (x' : nadd) (B1 : nat) (h1 : term99 x x' B1) : (term105 x x' n B1) = (and True).
Proof. exact (MK_COMB (@lem1274376) (@lem1274375 n x x' B1 h1)). Qed.
Lemma lem1274379 (n : nat) (y : nadd) (y' : nadd) (B2 : nat) (h1 : term99 y y' B2) : (term104 y y' n B2) = True.
Proof. exact (EQ_MP (@lem1274370 y y' n B2) (@lem1274369 n y y' B2 h1)). Qed.
Lemma lem1274380 (n : nat) (x : nadd) (x' : nadd) (B1 : nat) (y : nadd) (y' : nadd) (B2 : nat) (h1 : term99 x x' B1) (h2 : term99 y y' B2) : (term106 x x' B1 y y' n B2) = (True /\ True).
Proof. exact (MK_COMB (@lem1274377 n x x' B1 h1) (@lem1274379 n y y' B2 h2)). Qed.
Lemma lem1274382 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1274383 : (True /\ True) = True.
Proof. exact (@lem1274382 True). Qed.
Lemma lem1274384 (n : nat) (x : nadd) (x' : nadd) (B1 : nat) (y : nadd) (y' : nadd) (B2 : nat) (h1 : term99 x x' B1) (h2 : term99 y y' B2) : (term106 x x' B1 y y' n B2) = True.
Proof. exact (TRANS (@lem1274380 n x x' B1 y y' B2 h1 h2) (@lem1274383)). Qed.
Lemma lem1274385 (n : nat) (x : nadd) (x' : nadd) (B1 : nat) (y : nadd) (y' : nadd) (B2 : nat) (h1 : term99 x x' B1) (h2 : term99 y y' B2) : True = (term106 x x' B1 y y' n B2).
Proof. exact (SYM (@lem1274384 n x x' B1 y y' B2 h1 h2)). Qed.
Lemma lem1274386 (n : nat) (x : nadd) (x' : nadd) (B1 : nat) (y : nadd) (y' : nadd) (B2 : nat) (h1 : term99 x x' B1) (h2 : term99 y y' B2) : term106 x x' B1 y y' n B2.
Proof. exact (EQ_MP (@lem1274385 n x x' B1 y y' B2 h1 h2) (@lem0)). Qed.
Lemma lem1274387 (n : nat) (x : nadd) (x' : nadd) (B1 : nat) (y : nadd) (y' : nadd) (B2 : nat) (h1 : term99 x x' B1) (h2 : term99 y y' B2) : term107 x x' y y' n B1 B2.
Proof. exact (@lem1274361 x x' y y' n B1 B2 (@lem1274386 n x x' B1 y y' B2 h1 h2)). Qed.
Lemma lem1274388 (n : nat) (x : nadd) (x' : nadd) (B1 : nat) (y : nadd) (y' : nadd) (B2 : nat) (h1 : term99 x x' B1) (h2 : term99 y y' B2) : term108 x y x' y' n B1 B2.
Proof. exact (@lem1274358 x y x' y' n B1 B2 (@lem1274387 n x x' B1 y y' B2 h1 h2)). Qed.
Lemma lem1274393 (x : nadd) (x' : nadd) (B1 : nat) (y : nadd) (y' : nadd) (B2 : nat) (h1 : term99 x x' B1) (h2 : term99 y y' B2) : term109 x y x' y' B1 B2.
Proof. exact (fun n : nat => @lem1274388 n x x' B1 y y' B2 h1 h2). Qed.
Lemma lem1274394 (x : nadd) (x' : nadd) (B1 : nat) (y : nadd) (y' : nadd) (B2 : nat) (h1 : term99 x x' B1) (h2 : term99 y y' B2) : term96 x y x' y'.
Proof. exact (ex_intro (term95 x y x' y') (Nat.add B1 B2) (@lem1274393 x x' B1 y y' B2 h1 h2)). Qed.
Lemma lem1274395 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term66 x x' y y') : term62 y y'.
Proof. exact (proj2 (@lem1274351 x x' y y' h1)). Qed.
Lemma lem1274396 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term66 x x' y y') : term62 x x'.
Proof. exact (proj1 (@lem1274351 x x' y y' h1)). Qed.
Lemma lem1274397 (x : nadd) (x' : nadd) (B1 : nat) (y : nadd) (y' : nadd) (h1 : term99 x x' B1) (h2 : term62 y y') : term96 x y x' y'.
Proof. exact (ex_elim (@lem1274352 y y' h2) (fun B2 : nat => fun h0 : term110 y y' B2 => @lem1274394 x x' B1 y y' B2 h1 h0)). Qed.
Lemma lem1274398 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term62 x x') (h2 : term62 y y') : term96 x y x' y'.
Proof. exact (ex_elim (@lem1274354 x x' h1) (fun B1 : nat => fun h0 : term110 x x' B1 => @lem1274397 x x' B1 y y' h0 h2)). Qed.
Lemma lem1274399 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term62 x x') (h2 : term66 x x' y y') : (term62 y y') = (term96 x y x' y').
Proof. exact (prop_ext (fun h3 : term62 y y' => @lem1274398 x x' y y' h1 h3) (fun h3 : term96 x y x' y' => @lem1274395 x x' y y' h2)). Qed.
Lemma lem1274400 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term62 x x') (h2 : term66 x x' y y') : term96 x y x' y'.
Proof. exact (EQ_MP (@lem1274399 x x' y y' h1 h2) (@lem1274395 x x' y y' h2)). Qed.
Lemma lem1274401 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term66 x x' y y') : (term62 x x') = (term96 x y x' y').
Proof. exact (prop_ext (fun h2 : term62 x x' => @lem1274400 x x' y y' h2 h1) (fun h2 : term96 x y x' y' => @lem1274396 x x' y y' h1)). Qed.
Lemma lem1274402 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term66 x x' y y') : term96 x y x' y'.
Proof. exact (EQ_MP (@lem1274401 x x' y y' h1) (@lem1274396 x x' y y' h1)). Qed.
Lemma lem1274403 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : term98 x y x' y'.
Proof. exact (fun h0 : term66 x x' y y' => @lem1274402 x x' y y' h0). Qed.
Lemma lem1274404 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : term97 x y x' y'.
Proof. exact (EQ_MP (@lem1274350 x y x' y') (@lem1274403 x y x' y')). Qed.
Lemma lem1274409 (x : nadd) (y : nadd) (x' : nadd) : term111 x y x'.
Proof. exact (fun y' : nadd => @lem1274404 x y x' y'). Qed.
Lemma lem1274414 (x : nadd) (x' : nadd) : term112 x x'.
Proof. exact (fun y : nadd => @lem1274409 x y x'). Qed.
Lemma lem1274419 (x : nadd) : term113 x.
Proof. exact (fun x' : nadd => @lem1274414 x x'). Qed.
Lemma lem1274424 : term114.
Proof. exact (fun x : nadd => @lem1274419 x). Qed.
