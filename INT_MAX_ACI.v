Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MAX_ACI_term_abbrevs.
Require Import REAL_MAX_ACI_spec.
Require Import thm2299888_spec.
Require Import thm2299889_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2305091 (z : real) (x : real) (y : real) : term0 z x y.
Proof. exact (proj2 (@lem1578322 z x y)). Qed.
Lemma lem2305092 (z : real) (x : real) (y : real) : term1 z x y.
Proof. exact (proj2 (@lem2305091 z x y)). Qed.
Lemma lem2305093 (x : real) (y : real) : term2 x y.
Proof. exact (proj2 (@lem2305092 (@el real) x y)). Qed.
Lemma lem2305094 (x : real) (y : real) : (term3 x y) = (real_max x y).
Proof. exact (proj2 (@lem2305093 x y)). Qed.
Lemma lem2305095 (x : real) : term4 x.
Proof. exact (fun y : real => @lem2305094 x y). Qed.
Lemma lem2305096 : term5.
Proof. exact (fun x : real => @lem2305095 x). Qed.
Lemma lem2305097 (x : int) : term6 x.
Proof. exact (@lem2305096 (real_of_int x)). Qed.
Lemma lem2305098 (x : int) : (term6 x) = (term7 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem2305099 (x : int) : term7 x.
Proof. exact (EQ_MP (@lem2305098 x) (@lem2305097 x)). Qed.
Lemma lem2305100 (x : int) (y : int) : term8 x y.
Proof. exact (@lem2305099 x (real_of_int y)). Qed.
Lemma lem2305101 (x : int) (y : int) : (term8 x y) = ((term9 x y) = (term10 x y)).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem2305102 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2305101 x y) (@lem2305100 x y)). Qed.
Lemma lem2305104 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305105 (x : int) : (term12 x) = (term12 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem2305106 (x : int) (y : int) : (term9 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem2305105 x) (@lem2305104 x y)). Qed.
Lemma lem2305108 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305109 (x : int) (y : int) : (term13 x y) = (term14 x y).
Proof. exact (@lem2305108 x (int_max x y)). Qed.
Lemma lem2305110 (x : int) (y : int) : (term9 x y) = (term14 x y).
Proof. exact (TRANS (@lem2305106 x y) (@lem2305109 x y)). Qed.
Lemma lem2305111 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2305112 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (MK_COMB (@lem2305111) (@lem2305110 x y)). Qed.
Lemma lem2305114 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305115 (x : int) (y : int) : ((term9 x y) = (term10 x y)) = ((term14 x y) = (term11 x y)).
Proof. exact (MK_COMB (@lem2305112 x y) (@lem2305114 x y)). Qed.
Lemma lem2305117 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2305118 (x : int) (y : int) : ((term14 x y) = (term11 x y)) = ((term17 x y) = (int_max x y)).
Proof. exact (@lem2305117 (term17 x y) (int_max x y)). Qed.
Lemma lem2305119 (x : int) (y : int) : ((term9 x y) = (term10 x y)) = ((term17 x y) = (int_max x y)).
Proof. exact (TRANS (@lem2305115 x y) (@lem2305118 x y)). Qed.
Lemma lem2305120 (x : int) (y : int) : (term17 x y) = (int_max x y).
Proof. exact (EQ_MP (@lem2305119 x y) (@lem2305102 x y)). Qed.
Lemma lem2305121 (x : real) : (real_max x x) = x.
Proof. exact (proj1 (@lem2305093 x (@el real))). Qed.
Lemma lem2305122 : term18.
Proof. exact (fun x : real => @lem2305121 x). Qed.
Lemma lem2305123 (x : int) : term19 x.
Proof. exact (@lem2305122 (real_of_int x)). Qed.
Lemma lem2305124 (x : int) : (term19 x) = ((term20 x) = (real_of_int x)).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem2305125 (x : int) : (term20 x) = (real_of_int x).
Proof. exact (EQ_MP (@lem2305124 x) (@lem2305123 x)). Qed.
Lemma lem2305127 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305128 (x : int) : (term20 x) = (term21 x).
Proof. exact (@lem2305127 x x). Qed.
Lemma lem2305129 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2305130 (x : int) : (term22 x) = (term23 x).
Proof. exact (MK_COMB (@lem2305129) (@lem2305128 x)). Qed.
Lemma lem2305131 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2305132 (x : int) : ((term20 x) = (real_of_int x)) = ((term21 x) = (real_of_int x)).
Proof. exact (MK_COMB (@lem2305130 x) (@lem2305131 x)). Qed.
Lemma lem2305134 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2305135 (x : int) : ((term21 x) = (real_of_int x)) = ((int_max x x) = x).
Proof. exact (@lem2305134 (int_max x x) x). Qed.
Lemma lem2305136 (x : int) : ((term20 x) = (real_of_int x)) = ((int_max x x) = x).
Proof. exact (TRANS (@lem2305132 x) (@lem2305135 x)). Qed.
Lemma lem2305137 (x : int) : (int_max x x) = x.
Proof. exact (EQ_MP (@lem2305136 x) (@lem2305125 x)). Qed.
Lemma lem2305138 (x : int) (y : int) : term24 x y.
Proof. exact (conj (@lem2305137 x) (@lem2305120 x y)). Qed.
Lemma lem2305139 (y : real) (x : real) (z : real) : (term25 x y z) = (term25 y x z).
Proof. exact (proj1 (@lem2305092 z x y)). Qed.
Lemma lem2305140 (y : real) (x : real) : term26 y x.
Proof. exact (fun z : real => @lem2305139 y x z). Qed.
Lemma lem2305141 (y : real) : term27 y.
Proof. exact (fun x : real => @lem2305140 y x). Qed.
Lemma lem2305142 : term28.
Proof. exact (fun y : real => @lem2305141 y). Qed.
Lemma lem2305143 (y : int) : term29 y.
Proof. exact (@lem2305142 (real_of_int y)). Qed.
Lemma lem2305144 (y : int) : (term29 y) = (term30 y).
Proof. exact (eq_refl (term29 y)). Qed.
Lemma lem2305145 (y : int) : term30 y.
Proof. exact (EQ_MP (@lem2305144 y) (@lem2305143 y)). Qed.
Lemma lem2305146 (y : int) (x : int) : term31 y x.
Proof. exact (@lem2305145 y (real_of_int x)). Qed.
Lemma lem2305147 (y : int) (x : int) : (term31 y x) = (term32 y x).
Proof. exact (eq_refl (term31 y x)). Qed.
Lemma lem2305148 (y : int) (x : int) : term32 y x.
Proof. exact (EQ_MP (@lem2305147 y x) (@lem2305146 y x)). Qed.
Lemma lem2305149 (y : int) (x : int) (z : int) : term33 y x z.
Proof. exact (@lem2305148 y x (real_of_int z)). Qed.
Lemma lem2305150 (y : int) (x : int) (z : int) : (term33 y x z) = ((term34 x y z) = (term34 y x z)).
Proof. exact (eq_refl (term33 y x z)). Qed.
Lemma lem2305151 (y : int) (x : int) (z : int) : (term34 x y z) = (term34 y x z).
Proof. exact (EQ_MP (@lem2305150 y x z) (@lem2305149 y x z)). Qed.
Lemma lem2305153 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305154 (y : int) (z : int) : (term10 y z) = (term11 y z).
Proof. exact (@lem2305153 y z). Qed.
Lemma lem2305155 (x : int) : (term12 x) = (term12 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem2305156 (x : int) (y : int) (z : int) : (term34 x y z) = (term35 x y z).
Proof. exact (MK_COMB (@lem2305155 x) (@lem2305154 y z)). Qed.
Lemma lem2305158 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305159 (x : int) (y : int) (z : int) : (term35 x y z) = (term36 x y z).
Proof. exact (@lem2305158 x (int_max y z)). Qed.
Lemma lem2305160 (x : int) (y : int) (z : int) : (term34 x y z) = (term36 x y z).
Proof. exact (TRANS (@lem2305156 x y z) (@lem2305159 x y z)). Qed.
Lemma lem2305161 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2305162 (x : int) (y : int) (z : int) : (term37 x y z) = (term38 x y z).
Proof. exact (MK_COMB (@lem2305161) (@lem2305160 x y z)). Qed.
Lemma lem2305164 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305165 (x : int) (z : int) : (term10 x z) = (term11 x z).
Proof. exact (@lem2305164 x z). Qed.
Lemma lem2305166 (y : int) : (term12 y) = (term12 y).
Proof. exact (eq_refl (term12 y)). Qed.
Lemma lem2305167 (y : int) (x : int) (z : int) : (term34 y x z) = (term35 y x z).
Proof. exact (MK_COMB (@lem2305166 y) (@lem2305165 x z)). Qed.
Lemma lem2305169 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305170 (y : int) (x : int) (z : int) : (term35 y x z) = (term36 y x z).
Proof. exact (@lem2305169 y (int_max x z)). Qed.
Lemma lem2305171 (y : int) (x : int) (z : int) : (term34 y x z) = (term36 y x z).
Proof. exact (TRANS (@lem2305167 y x z) (@lem2305170 y x z)). Qed.
Lemma lem2305172 (y : int) (x : int) (z : int) : ((term34 x y z) = (term34 y x z)) = ((term36 x y z) = (term36 y x z)).
Proof. exact (MK_COMB (@lem2305162 x y z) (@lem2305171 y x z)). Qed.
Lemma lem2305174 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2305175 (y : int) (x : int) (z : int) : ((term36 x y z) = (term36 y x z)) = ((term39 x y z) = (term39 y x z)).
Proof. exact (@lem2305174 (term39 x y z) (term39 y x z)). Qed.
Lemma lem2305176 (y : int) (x : int) (z : int) : ((term34 x y z) = (term34 y x z)) = ((term39 x y z) = (term39 y x z)).
Proof. exact (TRANS (@lem2305172 y x z) (@lem2305175 y x z)). Qed.
Lemma lem2305177 (y : int) (x : int) (z : int) : (term39 x y z) = (term39 y x z).
Proof. exact (EQ_MP (@lem2305176 y x z) (@lem2305151 y x z)). Qed.
Lemma lem2305178 (z : int) (x : int) (y : int) : term40 z x y.
Proof. exact (conj (@lem2305177 y x z) (@lem2305138 x y)). Qed.
Lemma lem2305179 (x : real) (y : real) (z : real) : (term41 x y z) = (term25 x y z).
Proof. exact (proj1 (@lem2305091 z x y)). Qed.
Lemma lem2305180 (x : real) (y : real) : term42 x y.
Proof. exact (fun z : real => @lem2305179 x y z). Qed.
Lemma lem2305181 (x : real) : term43 x.
Proof. exact (fun y : real => @lem2305180 x y). Qed.
Lemma lem2305182 : term44.
Proof. exact (fun x : real => @lem2305181 x). Qed.
Lemma lem2305183 (x : int) : term45 x.
Proof. exact (@lem2305182 (real_of_int x)). Qed.
Lemma lem2305184 (x : int) : (term45 x) = (term46 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem2305185 (x : int) : term46 x.
Proof. exact (EQ_MP (@lem2305184 x) (@lem2305183 x)). Qed.
Lemma lem2305186 (x : int) (y : int) : term47 x y.
Proof. exact (@lem2305185 x (real_of_int y)). Qed.
Lemma lem2305187 (x : int) (y : int) : (term47 x y) = (term48 x y).
Proof. exact (eq_refl (term47 x y)). Qed.
Lemma lem2305188 (x : int) (y : int) : term48 x y.
Proof. exact (EQ_MP (@lem2305187 x y) (@lem2305186 x y)). Qed.
Lemma lem2305189 (x : int) (y : int) (z : int) : term49 x y z.
Proof. exact (@lem2305188 x y (real_of_int z)). Qed.
Lemma lem2305190 (x : int) (y : int) (z : int) : (term49 x y z) = ((term50 x y z) = (term34 x y z)).
Proof. exact (eq_refl (term49 x y z)). Qed.
Lemma lem2305191 (x : int) (y : int) (z : int) : (term50 x y z) = (term34 x y z).
Proof. exact (EQ_MP (@lem2305190 x y z) (@lem2305189 x y z)). Qed.
Lemma lem2305193 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305194 : real_max = real_max.
Proof. exact (eq_refl real_max). Qed.
Lemma lem2305195 (x : int) (y : int) : (term51 x y) = (term52 x y).
Proof. exact (MK_COMB (@lem2305194) (@lem2305193 x y)). Qed.
Lemma lem2305196 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2305197 (x : int) (y : int) (z : int) : (term50 x y z) = (term53 x y z).
Proof. exact (MK_COMB (@lem2305195 x y) (@lem2305196 z)). Qed.
Lemma lem2305199 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305200 (x : int) (y : int) (z : int) : (term53 x y z) = (term54 x y z).
Proof. exact (@lem2305199 (int_max x y) z). Qed.
Lemma lem2305201 (x : int) (y : int) (z : int) : (term50 x y z) = (term54 x y z).
Proof. exact (TRANS (@lem2305197 x y z) (@lem2305200 x y z)). Qed.
Lemma lem2305202 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2305203 (x : int) (y : int) (z : int) : (term55 x y z) = (term56 x y z).
Proof. exact (MK_COMB (@lem2305202) (@lem2305201 x y z)). Qed.
Lemma lem2305205 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305206 (y : int) (z : int) : (term10 y z) = (term11 y z).
Proof. exact (@lem2305205 y z). Qed.
Lemma lem2305207 (x : int) : (term12 x) = (term12 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem2305208 (x : int) (y : int) (z : int) : (term34 x y z) = (term35 x y z).
Proof. exact (MK_COMB (@lem2305207 x) (@lem2305206 y z)). Qed.
Lemma lem2305210 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305211 (x : int) (y : int) (z : int) : (term35 x y z) = (term36 x y z).
Proof. exact (@lem2305210 x (int_max y z)). Qed.
Lemma lem2305212 (x : int) (y : int) (z : int) : (term34 x y z) = (term36 x y z).
Proof. exact (TRANS (@lem2305208 x y z) (@lem2305211 x y z)). Qed.
Lemma lem2305213 (x : int) (y : int) (z : int) : ((term50 x y z) = (term34 x y z)) = ((term54 x y z) = (term36 x y z)).
Proof. exact (MK_COMB (@lem2305203 x y z) (@lem2305212 x y z)). Qed.
Lemma lem2305215 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2305216 (x : int) (y : int) (z : int) : ((term54 x y z) = (term36 x y z)) = ((term57 x y z) = (term39 x y z)).
Proof. exact (@lem2305215 (term57 x y z) (term39 x y z)). Qed.
Lemma lem2305217 (x : int) (y : int) (z : int) : ((term50 x y z) = (term34 x y z)) = ((term57 x y z) = (term39 x y z)).
Proof. exact (TRANS (@lem2305213 x y z) (@lem2305216 x y z)). Qed.
Lemma lem2305218 (x : int) (y : int) (z : int) : (term57 x y z) = (term39 x y z).
Proof. exact (EQ_MP (@lem2305217 x y z) (@lem2305191 x y z)). Qed.
Lemma lem2305219 (z : int) (x : int) (y : int) : term58 z x y.
Proof. exact (conj (@lem2305218 x y z) (@lem2305178 z x y)). Qed.
Lemma lem2305220 (y : real) (x : real) : (real_max x y) = (real_max y x).
Proof. exact (proj1 (@lem1578322 (@el real) x y)). Qed.
Lemma lem2305221 (y : real) : term59 y.
Proof. exact (fun x : real => @lem2305220 y x). Qed.
Lemma lem2305222 : term60.
Proof. exact (fun y : real => @lem2305221 y). Qed.
Lemma lem2305223 (y : int) : term61 y.
Proof. exact (@lem2305222 (real_of_int y)). Qed.
Lemma lem2305224 (y : int) : (term61 y) = (term62 y).
Proof. exact (eq_refl (term61 y)). Qed.
Lemma lem2305225 (y : int) : term62 y.
Proof. exact (EQ_MP (@lem2305224 y) (@lem2305223 y)). Qed.
Lemma lem2305226 (y : int) (x : int) : term63 y x.
Proof. exact (@lem2305225 y (real_of_int x)). Qed.
Lemma lem2305227 (y : int) (x : int) : (term63 y x) = ((term10 x y) = (term10 y x)).
Proof. exact (eq_refl (term63 y x)). Qed.
Lemma lem2305228 (y : int) (x : int) : (term10 x y) = (term10 y x).
Proof. exact (EQ_MP (@lem2305227 y x) (@lem2305226 y x)). Qed.
Lemma lem2305230 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305231 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2305232 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem2305231) (@lem2305230 x y)). Qed.
Lemma lem2305234 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305235 (y : int) (x : int) : (term10 y x) = (term11 y x).
Proof. exact (@lem2305234 y x). Qed.
Lemma lem2305236 (y : int) (x : int) : ((term10 x y) = (term10 y x)) = ((term11 x y) = (term11 y x)).
Proof. exact (MK_COMB (@lem2305232 x y) (@lem2305235 y x)). Qed.
Lemma lem2305238 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2305239 (y : int) (x : int) : ((term11 x y) = (term11 y x)) = ((int_max x y) = (int_max y x)).
Proof. exact (@lem2305238 (int_max x y) (int_max y x)). Qed.
Lemma lem2305240 (y : int) (x : int) : ((term10 x y) = (term10 y x)) = ((int_max x y) = (int_max y x)).
Proof. exact (TRANS (@lem2305236 y x) (@lem2305239 y x)). Qed.
Lemma lem2305241 (y : int) (x : int) : (int_max x y) = (int_max y x).
Proof. exact (EQ_MP (@lem2305240 y x) (@lem2305228 y x)). Qed.
Lemma lem2305242 (z : int) (x : int) (y : int) : term66 z x y.
Proof. exact (conj (@lem2305241 y x) (@lem2305219 z x y)). Qed.
