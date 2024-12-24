Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REVERSE_REVERSE_term_abbrevs.
Require Import REVERSE_APPEND_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1095962_spec.
Require Import thm1096517_spec.
Require Import thm1096523_spec.
Require Import thm1096524_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1112109 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1112110 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (@lem1112109 A P). Qed.
Lemma lem1112111 {A : Type'} : term1 A.
Proof. exact (@lem1112110 A (term2 A)). Qed.
Lemma lem1112112 {A : Type'} : (term3 A) = ((term4 A) = (@nil A)).
Proof. exact (eq_refl (term3 A)). Qed.
Lemma lem1112113 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1112114 {A : Type'} : (term5 A) = (term6 A).
Proof. exact (MK_COMB (@lem1112113) (@lem1112112 A)). Qed.
Lemma lem1112115 {A : Type'} (t : list A) : (term7 A t) = ((term8 A t) = t).
Proof. exact (eq_refl (term7 A t)). Qed.
Lemma lem1112116 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1112117 {A : Type'} (t : list A) : (term9 A t) = (term10 A t).
Proof. exact (MK_COMB (@lem1112116) (@lem1112115 A t)). Qed.
Lemma lem1112118 {A : Type'} (h : A) (t : list A) : (term11 A h t) = ((term12 A h t) = (@cons A h t)).
Proof. exact (eq_refl (term11 A h t)). Qed.
Lemma lem1112119 {A : Type'} (h : A) (t : list A) : (term13 A h t) = (term14 A h t).
Proof. exact (MK_COMB (@lem1112117 A t) (@lem1112118 A h t)). Qed.
Lemma lem1112120 {A : Type'} (h : A) : (term15 A h) = (term16 A h).
Proof. exact (fun_ext (fun t : list A => @lem1112119 A h t)). Qed.
Lemma lem1112121 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1112122 {A : Type'} (h : A) : (term17 A h) = (term18 A h).
Proof. exact (MK_COMB (@lem1112121 A) (@lem1112120 A h)). Qed.
Lemma lem1112123 {A : Type'} : (term19 A) = (term20 A).
Proof. exact (fun_ext (fun h : A => @lem1112122 A h)). Qed.
Lemma lem1112124 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1112125 {A : Type'} : (term21 A) = (term22 A).
Proof. exact (MK_COMB (@lem1112124 A) (@lem1112123 A)). Qed.
Lemma lem1112126 {A : Type'} : (term23 A) = (term24 A).
Proof. exact (MK_COMB (@lem1112114 A) (@lem1112125 A)). Qed.
Lemma lem1112127 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1112128 {A : Type'} : (term25 A) = (term26 A).
Proof. exact (MK_COMB (@lem1112127) (@lem1112126 A)). Qed.
Lemma lem1112129 {A : Type'} (l : list A) : (term7 A l) = ((term8 A l) = l).
Proof. exact (eq_refl (term7 A l)). Qed.
Lemma lem1112130 {A : Type'} : (term27 A) = (term2 A).
Proof. exact (fun_ext (fun l : list A => @lem1112129 A l)). Qed.
Lemma lem1112131 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1112132 {A : Type'} : (term28 A) = (term29 A).
Proof. exact (MK_COMB (@lem1112131 A) (@lem1112130 A)). Qed.
Lemma lem1112133 {A : Type'} : (term1 A) = (term30 A).
Proof. exact (MK_COMB (@lem1112128 A) (@lem1112132 A)). Qed.
Lemma lem1112134 {A : Type'} : term30 A.
Proof. exact (EQ_MP (@lem1112133 A) (@lem1112111 A)). Qed.
Lemma lem1112161 {A : Type'} : (@List.rev A (@nil A)) = (@nil A).
Proof. exact (proj1 (@lem1096517 A)). Qed.
Lemma lem1112162 {A : Type'} : (@List.rev A) = (@List.rev A).
Proof. exact (eq_refl (@List.rev A)). Qed.
Lemma lem1112163 {A : Type'} : (term4 A) = (@List.rev A (@nil A)).
Proof. exact (MK_COMB (@lem1112162 A) (@lem1112161 A)). Qed.
Lemma lem1112165 {A : Type'} : (@List.rev A (@nil A)) = (@nil A).
Proof. exact (proj1 (@lem1096517 A)). Qed.
Lemma lem1112166 {A : Type'} : (term4 A) = (@nil A).
Proof. exact (TRANS (@lem1112163 A) (@lem1112165 A)). Qed.
Lemma lem1112167 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1112168 {A : Type'} : (term31 A) = (@eq (list A) (@nil A)).
Proof. exact (MK_COMB (@lem1112167 A) (@lem1112166 A)). Qed.
Lemma lem1112169 {A : Type'} : (@nil A) = (@nil A).
Proof. exact (eq_refl (@nil A)). Qed.
Lemma lem1112170 {A : Type'} : ((term4 A) = (@nil A)) = ((@nil A) = (@nil A)).
Proof. exact (MK_COMB (@lem1112168 A) (@lem1112169 A)). Qed.
Lemma lem1112172 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1112173 {A : Type'} (x : list A) : (x = x) = True.
Proof. exact (@lem1112172 (list A) x). Qed.
Lemma lem1112174 {A : Type'} : ((@nil A) = (@nil A)) = True.
Proof. exact (@lem1112173 A (@nil A)). Qed.
Lemma lem1112175 {A : Type'} : ((term4 A) = (@nil A)) = True.
Proof. exact (TRANS (@lem1112170 A) (@lem1112174 A)). Qed.
Lemma lem1112176 {A : Type'} : True = ((term4 A) = (@nil A)).
Proof. exact (SYM (@lem1112175 A)). Qed.
Lemma lem1112177 {A : Type'} : (term4 A) = (@nil A).
Proof. exact (EQ_MP (@lem1112176 A) (@lem0)). Qed.
Lemma lem1112178 {A : Type'} : term32 A.
Proof. exact (proj2 (@lem1095962 A)). Qed.
Lemma lem1112179 {A : Type'} (h : A) : term33 A h.
Proof. exact (@lem1112178 A h). Qed.
Lemma lem1112180 {A : Type'} (h : A) : (term33 A h) = (term34 A h).
Proof. exact (eq_refl (term33 A h)). Qed.
Lemma lem1112181 {A : Type'} (h : A) : term34 A h.
Proof. exact (EQ_MP (@lem1112180 A h) (@lem1112179 A h)). Qed.
Lemma lem1112182 {A : Type'} (h : A) (t : list A) : term35 A h t.
Proof. exact (@lem1112181 A h t). Qed.
Lemma lem1112183 {A : Type'} (h : A) (t : list A) : (term35 A h t) = (term36 A h t).
Proof. exact (eq_refl (term35 A h t)). Qed.
Lemma lem1112184 {A : Type'} (h : A) (t : list A) : term36 A h t.
Proof. exact (EQ_MP (@lem1112183 A h t) (@lem1112182 A h t)). Qed.
Lemma lem1112185 {A : Type'} (h : A) (t : list A) (l : list A) : term37 A h t l.
Proof. exact (@lem1112184 A h t l). Qed.
Lemma lem1112186 {A : Type'} (h : A) (t : list A) (l : list A) : (term37 A h t l) = ((term38 A h t l) = (term39 A h t l)).
Proof. exact (eq_refl (term37 A h t l)). Qed.
Lemma lem1112188 {A : Type'} : term40 A.
Proof. exact (proj1 (@lem1095962 A)). Qed.
Lemma lem1112189 {A : Type'} (l : list A) : term41 A l.
Proof. exact (@lem1112188 A l). Qed.
Lemma lem1112190 {A : Type'} (l : list A) : (term41 A l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl (term41 A l)). Qed.
Lemma lem1112192 {A : Type'} (l : list A) : term42 A l.
Proof. exact (@lem1112107 A l). Qed.
Lemma lem1112193 {A : Type'} (l : list A) : (term42 A l) = (term43 A l).
Proof. exact (eq_refl (term42 A l)). Qed.
Lemma lem1112194 {A : Type'} (l : list A) : term43 A l.
Proof. exact (EQ_MP (@lem1112193 A l) (@lem1112192 A l)). Qed.
Lemma lem1112195 {A : Type'} (l : list A) (m : list A) : term44 A l m.
Proof. exact (@lem1112194 A l m). Qed.
Lemma lem1112196 {A : Type'} (m : list A) (l : list A) : (term44 A l m) = ((term45 A l m) = (term46 A m l)).
Proof. exact (eq_refl (term44 A l m)). Qed.
Lemma lem1112203 {A : Type'} (l : list A) (x : A) : (term47 A x l) = (term48 A l x).
Proof. exact (EQ_MP (@lem1096524 A l x) (@lem1096523 A l x)). Qed.
Lemma lem1112204 {A : Type'} (l : list A) (x : A) : (term47 A x l) = (term48 A l x).
Proof. exact (@lem1112203 A l x). Qed.
Lemma lem1112205 {A : Type'} (t : list A) (h : A) : (term47 A h t) = (term48 A t h).
Proof. exact (@lem1112204 A t h). Qed.
Lemma lem1112206 {A : Type'} : (@List.rev A) = (@List.rev A).
Proof. exact (eq_refl (@List.rev A)). Qed.
Lemma lem1112207 {A : Type'} (t : list A) (h : A) : (term12 A h t) = (term49 A t h).
Proof. exact (MK_COMB (@lem1112206 A) (@lem1112205 A t h)). Qed.
Lemma lem1112209 {A : Type'} (m : list A) (l : list A) : (term45 A l m) = (term46 A m l).
Proof. exact (EQ_MP (@lem1112196 A m l) (@lem1112195 A l m)). Qed.
Lemma lem1112210 {A : Type'} (m : list A) (l : list A) : (term45 A l m) = (term46 A m l).
Proof. exact (@lem1112209 A m l). Qed.
Lemma lem1112211 {A : Type'} (h : A) (t : list A) : (term49 A t h) = (term50 A h t).
Proof. exact (@lem1112210 A (@cons A h (@nil A)) (@List.rev A t)). Qed.
Lemma lem1112213 {A : Type'} (l : list A) (x : A) : (term47 A x l) = (term48 A l x).
Proof. exact (EQ_MP (@lem1096524 A l x) (@lem1096523 A l x)). Qed.
Lemma lem1112214 {A : Type'} (l : list A) (x : A) : (term47 A x l) = (term48 A l x).
Proof. exact (@lem1112213 A l x). Qed.
Lemma lem1112215 {A : Type'} (h : A) : (term51 A h) = (term52 A h).
Proof. exact (@lem1112214 A (@nil A) h). Qed.
Lemma lem1112217 {A : Type'} : (@List.rev A (@nil A)) = (@nil A).
Proof. exact (proj1 (@lem1096517 A)). Qed.
Lemma lem1112218 {A : Type'} : (@List.app A) = (@List.app A).
Proof. exact (eq_refl (@List.app A)). Qed.
Lemma lem1112219 {A : Type'} : (term53 A) = (@List.app A (@nil A)).
Proof. exact (MK_COMB (@lem1112218 A) (@lem1112217 A)). Qed.
Lemma lem1112220 {A : Type'} (h : A) : (@cons A h (@nil A)) = (@cons A h (@nil A)).
Proof. exact (eq_refl (@cons A h (@nil A))). Qed.
Lemma lem1112221 {A : Type'} (h : A) : (term52 A h) = (term54 A h).
Proof. exact (MK_COMB (@lem1112219 A) (@lem1112220 A h)). Qed.
Lemma lem1112223 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1112190 A l) (@lem1112189 A l)). Qed.
Lemma lem1112224 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (@lem1112223 A l). Qed.
Lemma lem1112225 {A : Type'} (h : A) : (term54 A h) = (@cons A h (@nil A)).
Proof. exact (@lem1112224 A (@cons A h (@nil A))). Qed.
Lemma lem1112226 {A : Type'} (h : A) : (term52 A h) = (@cons A h (@nil A)).
Proof. exact (TRANS (@lem1112221 A h) (@lem1112225 A h)). Qed.
Lemma lem1112227 {A : Type'} (h : A) : (term51 A h) = (@cons A h (@nil A)).
Proof. exact (TRANS (@lem1112215 A h) (@lem1112226 A h)). Qed.
Lemma lem1112228 {A : Type'} : (@List.app A) = (@List.app A).
Proof. exact (eq_refl (@List.app A)). Qed.
Lemma lem1112229 {A : Type'} (h : A) : (term55 A h) = (term56 A h).
Proof. exact (MK_COMB (@lem1112228 A) (@lem1112227 A h)). Qed.
Lemma lem1112231 {A : Type'} (t : list A) (h1 : (term8 A t) = t) : (term8 A t) = t.
Proof. exact (h1). Qed.
Lemma lem1112232 {A : Type'} (h : A) (t : list A) (h1 : (term8 A t) = t) : (term50 A h t) = (term57 A h t).
Proof. exact (MK_COMB (@lem1112229 A h) (@lem1112231 A t h1)). Qed.
Lemma lem1112234 {A : Type'} (h : A) (t : list A) (l : list A) : (term38 A h t l) = (term39 A h t l).
Proof. exact (EQ_MP (@lem1112186 A h t l) (@lem1112185 A h t l)). Qed.
Lemma lem1112235 {A : Type'} (h : A) (t : list A) (l : list A) : (term38 A h t l) = (term39 A h t l).
Proof. exact (@lem1112234 A h t l). Qed.
Lemma lem1112236 {A : Type'} (h : A) (t : list A) : (term57 A h t) = (term58 A h t).
Proof. exact (@lem1112235 A h (@nil A) t). Qed.
Lemma lem1112238 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1112190 A l) (@lem1112189 A l)). Qed.
Lemma lem1112239 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (@lem1112238 A l). Qed.
Lemma lem1112240 {A : Type'} (t : list A) : (@List.app A (@nil A) t) = t.
Proof. exact (@lem1112239 A t). Qed.
Lemma lem1112241 {A : Type'} (h : A) : (@cons A h) = (@cons A h).
Proof. exact (eq_refl (@cons A h)). Qed.
Lemma lem1112242 {A : Type'} (h : A) (t : list A) : (term58 A h t) = (@cons A h t).
Proof. exact (MK_COMB (@lem1112241 A h) (@lem1112240 A t)). Qed.
Lemma lem1112243 {A : Type'} (h : A) (t : list A) : (term57 A h t) = (@cons A h t).
Proof. exact (TRANS (@lem1112236 A h t) (@lem1112242 A h t)). Qed.
Lemma lem1112244 {A : Type'} (h : A) (t : list A) (h1 : (term8 A t) = t) : (term50 A h t) = (@cons A h t).
Proof. exact (TRANS (@lem1112232 A h t h1) (@lem1112243 A h t)). Qed.
Lemma lem1112245 {A : Type'} (h : A) (t : list A) (h1 : (term8 A t) = t) : (term49 A t h) = (@cons A h t).
Proof. exact (TRANS (@lem1112211 A h t) (@lem1112244 A h t h1)). Qed.
Lemma lem1112246 {A : Type'} (h : A) (t : list A) (h1 : (term8 A t) = t) : (term12 A h t) = (@cons A h t).
Proof. exact (TRANS (@lem1112207 A t h) (@lem1112245 A h t h1)). Qed.
Lemma lem1112247 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1112248 {A : Type'} (h : A) (t : list A) (h1 : (term8 A t) = t) : (term59 A h t) = (term60 A h t).
Proof. exact (MK_COMB (@lem1112247 A) (@lem1112246 A h t h1)). Qed.
Lemma lem1112249 {A : Type'} (h : A) (t : list A) : (@cons A h t) = (@cons A h t).
Proof. exact (eq_refl (@cons A h t)). Qed.
Lemma lem1112250 {A : Type'} (h : A) (t : list A) (h1 : (term8 A t) = t) : ((term12 A h t) = (@cons A h t)) = ((@cons A h t) = (@cons A h t)).
Proof. exact (MK_COMB (@lem1112248 A h t h1) (@lem1112249 A h t)). Qed.
Lemma lem1112252 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1112253 {A : Type'} (x : list A) : (x = x) = True.
Proof. exact (@lem1112252 (list A) x). Qed.
Lemma lem1112254 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@cons A h t)) = True.
Proof. exact (@lem1112253 A (@cons A h t)). Qed.
Lemma lem1112255 {A : Type'} (h : A) (t : list A) (h1 : (term8 A t) = t) : ((term12 A h t) = (@cons A h t)) = True.
Proof. exact (TRANS (@lem1112250 A h t h1) (@lem1112254 A h t)). Qed.
Lemma lem1112256 {A : Type'} (h : A) (t : list A) (h1 : (term8 A t) = t) : True = ((term12 A h t) = (@cons A h t)).
Proof. exact (SYM (@lem1112255 A h t h1)). Qed.
Lemma lem1112257 {A : Type'} (h : A) (t : list A) (h1 : (term8 A t) = t) : (term12 A h t) = (@cons A h t).
Proof. exact (EQ_MP (@lem1112256 A h t h1) (@lem0)). Qed.
Lemma lem1112258 {A : Type'} (h : A) (t : list A) : term14 A h t.
Proof. exact (fun h0 : (term8 A t) = t => @lem1112257 A h t h0). Qed.
Lemma lem1112263 {A : Type'} (h : A) : term18 A h.
Proof. exact (fun t : list A => @lem1112258 A h t). Qed.
Lemma lem1112268 {A : Type'} : term22 A.
Proof. exact (fun h : A => @lem1112263 A h). Qed.
Lemma lem1112269 {A : Type'} : term24 A.
Proof. exact (conj (@lem1112177 A) (@lem1112268 A)). Qed.
Lemma lem1112270 {A : Type'} : term29 A.
Proof. exact (@lem1112134 A (@lem1112269 A)). Qed.
