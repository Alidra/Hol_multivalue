Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1108204_term_abbrevs.
Require Import thm1107739_spec.
Require Import thm1108123_spec.
Lemma lem1108124 {_25645 _25647 _25655 : Type'} : (term0 _25645 _25647 _25655) = (term1 _25645 _25647 _25655).
Proof. exact (eq_refl (term0 _25645 _25647 _25655)). Qed.
Lemma lem1108125 {_25645 _25647 _25655 : Type'} : term1 _25645 _25647 _25655.
Proof. exact (EQ_MP (@lem1108124 _25645 _25647 _25655) (@lem1107739 _25645 _25647 _25655)). Qed.
Lemma lem1108126 {_25645 _25647 _25655 : Type'} : term2 _25645 _25647 _25655.
Proof. exact (@lem1108125 _25645 _25647 _25655 term3). Qed.
Lemma lem1108127 {_25645 _25647 _25655 : Type'} : (term2 _25645 _25647 _25655) = (term4 _25645 _25647 _25655).
Proof. exact (eq_refl (term2 _25645 _25647 _25655)). Qed.
Lemma lem1108128 {_25645 _25647 _25655 : Type'} : term4 _25645 _25647 _25655.
Proof. exact (EQ_MP (@lem1108127 _25645 _25647 _25655) (@lem1108126 _25645 _25647 _25655)). Qed.
Lemma lem1108129 {_25645 _25647 _25655 : Type'} (h1 : (@ITLIST2 _25645 _25647 _25655) = (term5 _25645 _25647 _25655)) : (@ITLIST2 _25645 _25647 _25655) = (term5 _25645 _25647 _25655).
Proof. exact (h1). Qed.
Lemma lem1108130 {_25645 _25647 _25655 : Type'} (h1 : (@ITLIST2 _25645 _25647 _25655) = (term5 _25645 _25647 _25655)) : (term5 _25645 _25647 _25655) = (@ITLIST2 _25645 _25647 _25655).
Proof. exact (SYM (@lem1108129 _25645 _25647 _25655 h1)). Qed.
Lemma lem1108131 {_25645 _25647 _25655 : Type'} (h1 : (term5 _25645 _25647 _25655) = (@ITLIST2 _25645 _25647 _25655)) : (term5 _25645 _25647 _25655) = (@ITLIST2 _25645 _25647 _25655).
Proof. exact (h1). Qed.
Lemma lem1108132 {_25645 _25647 _25655 : Type'} (h1 : (term5 _25645 _25647 _25655) = (@ITLIST2 _25645 _25647 _25655)) : (@ITLIST2 _25645 _25647 _25655) = (term5 _25645 _25647 _25655).
Proof. exact (SYM (@lem1108131 _25645 _25647 _25655 h1)). Qed.
Lemma lem1108133 {_25645 _25647 _25655 : Type'} : ((@ITLIST2 _25645 _25647 _25655) = (term5 _25645 _25647 _25655)) = ((term5 _25645 _25647 _25655) = (@ITLIST2 _25645 _25647 _25655)).
Proof. exact (prop_ext (fun h1 : (@ITLIST2 _25645 _25647 _25655) = (term5 _25645 _25647 _25655) => @lem1108130 _25645 _25647 _25655 h1) (fun h1 : (term5 _25645 _25647 _25655) = (@ITLIST2 _25645 _25647 _25655) => @lem1108132 _25645 _25647 _25655 h1)). Qed.
Lemma lem1108136 {_25645 _25647 _25655 : Type'} : (term5 _25645 _25647 _25655) = (@ITLIST2 _25645 _25647 _25655).
Proof. exact (EQ_MP (@lem1108133 _25645 _25647 _25655) (@lem1108123 _25645 _25647 _25655)). Qed.
Lemma lem1108137 {_25645 _25647 _25655 : Type'} : (term5 _25645 _25647 _25655) = (@ITLIST2 _25645 _25647 _25655).
Proof. exact (@lem1108136 _25645 _25647 _25655). Qed.
Lemma lem1108138 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1108139 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) : (term6 _25645 _25647 _25655 f) = (@ITLIST2 _25645 _25647 _25655 f).
Proof. exact (MK_COMB (@lem1108137 _25645 _25647 _25655) (@lem1108138 _25645 _25647 _25655 f)). Qed.
Lemma lem1108140 {_25647 : Type'} : (@nil _25647) = (@nil _25647).
Proof. exact (eq_refl (@nil _25647)). Qed.
Lemma lem1108141 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) : (term7 _25645 _25647 _25655 f) = (@ITLIST2 _25645 _25647 _25655 f (@nil _25647)).
Proof. exact (MK_COMB (@lem1108139 _25645 _25647 _25655 f) (@lem1108140 _25647)). Qed.
Lemma lem1108142 {_25655 : Type'} (l2 : list _25655) : l2 = l2.
Proof. exact (eq_refl l2). Qed.
Lemma lem1108143 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) (l2 : list _25655) : (term8 _25645 _25647 _25655 f l2) = (@ITLIST2 _25645 _25647 _25655 f (@nil _25647) l2).
Proof. exact (MK_COMB (@lem1108141 _25645 _25647 _25655 f) (@lem1108142 _25655 l2)). Qed.
Lemma lem1108144 {_25645 : Type'} (b : _25645) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1108145 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) (l2 : list _25655) (b : _25645) : (term9 _25645 _25647 _25655 f l2 b) = (@ITLIST2 _25645 _25647 _25655 f (@nil _25647) l2 b).
Proof. exact (MK_COMB (@lem1108143 _25645 _25647 _25655 f l2) (@lem1108144 _25645 b)). Qed.
Lemma lem1108146 {_25645 : Type'} : (@eq _25645) = (@eq _25645).
Proof. exact (eq_refl (@eq _25645)). Qed.
Lemma lem1108147 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) (l2 : list _25655) (b : _25645) : (term10 _25645 _25647 _25655 f l2 b) = (term11 _25645 _25647 _25655 f l2 b).
Proof. exact (MK_COMB (@lem1108146 _25645) (@lem1108145 _25645 _25647 _25655 f l2 b)). Qed.
Lemma lem1108148 {_25645 : Type'} (b : _25645) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1108149 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) (l2 : list _25655) (b : _25645) : ((term9 _25645 _25647 _25655 f l2 b) = b) = ((@ITLIST2 _25645 _25647 _25655 f (@nil _25647) l2 b) = b).
Proof. exact (MK_COMB (@lem1108147 _25645 _25647 _25655 f l2 b) (@lem1108148 _25645 b)). Qed.
Lemma lem1108150 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) (l2 : list _25655) : (term12 _25645 _25647 _25655 f l2) = (term13 _25645 _25647 _25655 f l2).
Proof. exact (fun_ext (fun b : _25645 => @lem1108149 _25645 _25647 _25655 f l2 b)). Qed.
Lemma lem1108151 {_25645 : Type'} : (@all _25645) = (@all _25645).
Proof. exact (eq_refl (@all _25645)). Qed.
Lemma lem1108152 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) (l2 : list _25655) : (term14 _25645 _25647 _25655 f l2) = (term15 _25645 _25647 _25655 f l2).
Proof. exact (MK_COMB (@lem1108151 _25645) (@lem1108150 _25645 _25647 _25655 f l2)). Qed.
Lemma lem1108153 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) : (term16 _25645 _25647 _25655 f) = (term17 _25645 _25647 _25655 f).
Proof. exact (fun_ext (fun l2 : list _25655 => @lem1108152 _25645 _25647 _25655 f l2)). Qed.
Lemma lem1108154 {_25655 : Type'} : (@all (list _25655)) = (@all (list _25655)).
Proof. exact (eq_refl (@all (list _25655))). Qed.
Lemma lem1108155 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) : (term18 _25645 _25647 _25655 f) = (term19 _25645 _25647 _25655 f).
Proof. exact (MK_COMB (@lem1108154 _25655) (@lem1108153 _25645 _25647 _25655 f)). Qed.
Lemma lem1108156 {_25645 _25647 _25655 : Type'} : (term20 _25645 _25647 _25655) = (term21 _25645 _25647 _25655).
Proof. exact (fun_ext (fun f : type1474 _25645 _25647 _25655 => @lem1108155 _25645 _25647 _25655 f)). Qed.
Lemma lem1108157 {_25645 _25647 _25655 : Type'} : (@all (_25647 -> _25655 -> _25645 -> _25645)) = (@all (_25647 -> _25655 -> _25645 -> _25645)).
Proof. exact (eq_refl (@all (_25647 -> _25655 -> _25645 -> _25645))). Qed.
Lemma lem1108158 {_25645 _25647 _25655 : Type'} : (term22 _25645 _25647 _25655) = (term23 _25645 _25647 _25655).
Proof. exact (MK_COMB (@lem1108157 _25645 _25647 _25655) (@lem1108156 _25645 _25647 _25655)). Qed.
Lemma lem1108159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1108160 {_25645 _25647 _25655 : Type'} : (term24 _25645 _25647 _25655) = (term25 _25645 _25647 _25655).
Proof. exact (MK_COMB (@lem1108159) (@lem1108158 _25645 _25647 _25655)). Qed.
Lemma lem1108162 {_25645 _25647 _25655 : Type'} : (term5 _25645 _25647 _25655) = (@ITLIST2 _25645 _25647 _25655).
Proof. exact (EQ_MP (@lem1108133 _25645 _25647 _25655) (@lem1108123 _25645 _25647 _25655)). Qed.
Lemma lem1108163 {_25645 _25647 _25655 : Type'} : (term5 _25645 _25647 _25655) = (@ITLIST2 _25645 _25647 _25655).
Proof. exact (@lem1108162 _25645 _25647 _25655). Qed.
Lemma lem1108164 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1108165 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) : (term6 _25645 _25647 _25655 f) = (@ITLIST2 _25645 _25647 _25655 f).
Proof. exact (MK_COMB (@lem1108163 _25645 _25647 _25655) (@lem1108164 _25645 _25647 _25655 f)). Qed.
Lemma lem1108166 {_25647 : Type'} (h1' : _25647) (t1 : list _25647) : (@cons _25647 h1' t1) = (@cons _25647 h1' t1).
Proof. exact (eq_refl (@cons _25647 h1' t1)). Qed.
Lemma lem1108167 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) (h1' : _25647) (t1 : list _25647) : (term26 _25645 _25647 _25655 f h1' t1) = (term27 _25645 _25647 _25655 f h1' t1).
Proof. exact (MK_COMB (@lem1108165 _25645 _25647 _25655 f) (@lem1108166 _25647 h1' t1)). Qed.
Lemma lem1108168 {_25655 : Type'} (l2 : list _25655) : l2 = l2.
Proof. exact (eq_refl l2). Qed.
Lemma lem1108169 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) (h1' : _25647) (t1 : list _25647) (l2 : list _25655) : (term28 _25645 _25647 _25655 f h1' t1 l2) = (term29 _25645 _25647 _25655 f h1' t1 l2).
Proof. exact (MK_COMB (@lem1108167 _25645 _25647 _25655 f h1' t1) (@lem1108168 _25655 l2)). Qed.
Lemma lem1108170 {_25645 : Type'} (b : _25645) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1108171 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) (h1' : _25647) (t1 : list _25647) (l2 : list _25655) (b : _25645) : (term30 _25645 _25647 _25655 f h1' t1 l2 b) = (term31 _25645 _25647 _25655 f h1' t1 l2 b).
Proof. exact (MK_COMB (@lem1108169 _25645 _25647 _25655 f h1' t1 l2) (@lem1108170 _25645 b)). Qed.
Lemma lem1108172 {_25645 : Type'} : (@eq _25645) = (@eq _25645).
Proof. exact (eq_refl (@eq _25645)). Qed.
Lemma lem1108173 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) (h1' : _25647) (t1 : list _25647) (l2 : list _25655) (b : _25645) : (term32 _25645 _25647 _25655 f h1' t1 l2 b) = (term33 _25645 _25647 _25655 f h1' t1 l2 b).
Proof. exact (MK_COMB (@lem1108172 _25645) (@lem1108171 _25645 _25647 _25655 f h1' t1 l2 b)). Qed.
Lemma lem1108175 {_25645 _25647 _25655 : Type'} : (term5 _25645 _25647 _25655) = (@ITLIST2 _25645 _25647 _25655).
Proof. exact (EQ_MP (@lem1108133 _25645 _25647 _25655) (@lem1108123 _25645 _25647 _25655)). Qed.
Lemma lem1108176 {_25645 _25647 _25655 : Type'} : (term5 _25645 _25647 _25655) = (@ITLIST2 _25645 _25647 _25655).
Proof. exact (@lem1108175 _25645 _25647 _25655). Qed.
Lemma lem1108177 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1108178 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) : (term6 _25645 _25647 _25655 f) = (@ITLIST2 _25645 _25647 _25655 f).
Proof. exact (MK_COMB (@lem1108176 _25645 _25647 _25655) (@lem1108177 _25645 _25647 _25655 f)). Qed.
Lemma lem1108179 {_25647 : Type'} (t1 : list _25647) : t1 = t1.
Proof. exact (eq_refl t1). Qed.
Lemma lem1108180 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) (t1 : list _25647) : (term34 _25645 _25647 _25655 f t1) = (@ITLIST2 _25645 _25647 _25655 f t1).
Proof. exact (MK_COMB (@lem1108178 _25645 _25647 _25655 f) (@lem1108179 _25647 t1)). Qed.
Lemma lem1108181 {_25655 : Type'} (l2 : list _25655) : (@tl _25655 l2) = (@tl _25655 l2).
Proof. exact (eq_refl (@tl _25655 l2)). Qed.
Lemma lem1108182 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) (t1 : list _25647) (l2 : list _25655) : (term35 _25645 _25647 _25655 f t1 l2) = (term36 _25645 _25647 _25655 f t1 l2).
Proof. exact (MK_COMB (@lem1108180 _25645 _25647 _25655 f t1) (@lem1108181 _25655 l2)). Qed.
Lemma lem1108183 {_25645 : Type'} (b : _25645) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1108184 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) (t1 : list _25647) (l2 : list _25655) (b : _25645) : (term37 _25645 _25647 _25655 f t1 l2 b) = (term38 _25645 _25647 _25655 f t1 l2 b).
Proof. exact (MK_COMB (@lem1108182 _25645 _25647 _25655 f t1 l2) (@lem1108183 _25645 b)). Qed.
Lemma lem1108185 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) (h1' : _25647) (l2 : list _25655) : (term39 _25645 _25647 _25655 f h1' l2) = (term39 _25645 _25647 _25655 f h1' l2).
Proof. exact (eq_refl (term39 _25645 _25647 _25655 f h1' l2)). Qed.
Lemma lem1108186 {_25645 _25647 _25655 : Type'} (h1' : _25647) (f : type1474 _25645 _25647 _25655) (t1 : list _25647) (l2 : list _25655) (b : _25645) : (term40 _25645 _25647 _25655 h1' f t1 l2 b) = (term41 _25645 _25647 _25655 h1' f t1 l2 b).
Proof. exact (MK_COMB (@lem1108185 _25645 _25647 _25655 f h1' l2) (@lem1108184 _25645 _25647 _25655 f t1 l2 b)). Qed.
Lemma lem1108187 {_25645 _25647 _25655 : Type'} (h1' : _25647) (f : type1474 _25645 _25647 _25655) (t1 : list _25647) (l2 : list _25655) (b : _25645) : ((term30 _25645 _25647 _25655 f h1' t1 l2 b) = (term40 _25645 _25647 _25655 h1' f t1 l2 b)) = ((term31 _25645 _25647 _25655 f h1' t1 l2 b) = (term41 _25645 _25647 _25655 h1' f t1 l2 b)).
Proof. exact (MK_COMB (@lem1108173 _25645 _25647 _25655 f h1' t1 l2 b) (@lem1108186 _25645 _25647 _25655 h1' f t1 l2 b)). Qed.
Lemma lem1108188 {_25645 _25647 _25655 : Type'} (h1' : _25647) (f : type1474 _25645 _25647 _25655) (t1 : list _25647) (l2 : list _25655) : (term42 _25645 _25647 _25655 h1' f t1 l2) = (term43 _25645 _25647 _25655 h1' f t1 l2).
Proof. exact (fun_ext (fun b : _25645 => @lem1108187 _25645 _25647 _25655 h1' f t1 l2 b)). Qed.
Lemma lem1108189 {_25645 : Type'} : (@all _25645) = (@all _25645).
Proof. exact (eq_refl (@all _25645)). Qed.
Lemma lem1108190 {_25645 _25647 _25655 : Type'} (h1' : _25647) (f : type1474 _25645 _25647 _25655) (t1 : list _25647) (l2 : list _25655) : (term44 _25645 _25647 _25655 h1' f t1 l2) = (term45 _25645 _25647 _25655 h1' f t1 l2).
Proof. exact (MK_COMB (@lem1108189 _25645) (@lem1108188 _25645 _25647 _25655 h1' f t1 l2)). Qed.
Lemma lem1108191 {_25645 _25647 _25655 : Type'} (h1' : _25647) (f : type1474 _25645 _25647 _25655) (t1 : list _25647) : (term46 _25645 _25647 _25655 h1' f t1) = (term47 _25645 _25647 _25655 h1' f t1).
Proof. exact (fun_ext (fun l2 : list _25655 => @lem1108190 _25645 _25647 _25655 h1' f t1 l2)). Qed.
Lemma lem1108192 {_25655 : Type'} : (@all (list _25655)) = (@all (list _25655)).
Proof. exact (eq_refl (@all (list _25655))). Qed.
Lemma lem1108193 {_25645 _25647 _25655 : Type'} (h1' : _25647) (f : type1474 _25645 _25647 _25655) (t1 : list _25647) : (term48 _25645 _25647 _25655 h1' f t1) = (term49 _25645 _25647 _25655 h1' f t1).
Proof. exact (MK_COMB (@lem1108192 _25655) (@lem1108191 _25645 _25647 _25655 h1' f t1)). Qed.
Lemma lem1108194 {_25645 _25647 _25655 : Type'} (h1' : _25647) (f : type1474 _25645 _25647 _25655) : (term50 _25645 _25647 _25655 h1' f) = (term51 _25645 _25647 _25655 h1' f).
Proof. exact (fun_ext (fun t1 : list _25647 => @lem1108193 _25645 _25647 _25655 h1' f t1)). Qed.
Lemma lem1108195 {_25647 : Type'} : (@all (list _25647)) = (@all (list _25647)).
Proof. exact (eq_refl (@all (list _25647))). Qed.
Lemma lem1108196 {_25645 _25647 _25655 : Type'} (h1' : _25647) (f : type1474 _25645 _25647 _25655) : (term52 _25645 _25647 _25655 h1' f) = (term53 _25645 _25647 _25655 h1' f).
Proof. exact (MK_COMB (@lem1108195 _25647) (@lem1108194 _25645 _25647 _25655 h1' f)). Qed.
Lemma lem1108197 {_25645 _25647 _25655 : Type'} (h1' : _25647) : (term54 _25645 _25647 _25655 h1') = (term55 _25645 _25647 _25655 h1').
Proof. exact (fun_ext (fun f : type1474 _25645 _25647 _25655 => @lem1108196 _25645 _25647 _25655 h1' f)). Qed.
Lemma lem1108198 {_25645 _25647 _25655 : Type'} : (@all (_25647 -> _25655 -> _25645 -> _25645)) = (@all (_25647 -> _25655 -> _25645 -> _25645)).
Proof. exact (eq_refl (@all (_25647 -> _25655 -> _25645 -> _25645))). Qed.
Lemma lem1108199 {_25645 _25647 _25655 : Type'} (h1' : _25647) : (term56 _25645 _25647 _25655 h1') = (term57 _25645 _25647 _25655 h1').
Proof. exact (MK_COMB (@lem1108198 _25645 _25647 _25655) (@lem1108197 _25645 _25647 _25655 h1')). Qed.
Lemma lem1108200 {_25645 _25647 _25655 : Type'} : (term58 _25645 _25647 _25655) = (term59 _25645 _25647 _25655).
Proof. exact (fun_ext (fun h1' : _25647 => @lem1108199 _25645 _25647 _25655 h1')). Qed.
Lemma lem1108201 {_25647 : Type'} : (@all _25647) = (@all _25647).
Proof. exact (eq_refl (@all _25647)). Qed.
Lemma lem1108202 {_25645 _25647 _25655 : Type'} : (term60 _25645 _25647 _25655) = (term61 _25645 _25647 _25655).
Proof. exact (MK_COMB (@lem1108201 _25647) (@lem1108200 _25645 _25647 _25655)). Qed.
Lemma lem1108203 {_25645 _25647 _25655 : Type'} : (term4 _25645 _25647 _25655) = (term62 _25645 _25647 _25655).
Proof. exact (MK_COMB (@lem1108160 _25645 _25647 _25655) (@lem1108202 _25645 _25647 _25655)). Qed.
Lemma lem1108204 {_25645 _25647 _25655 : Type'} : term62 _25645 _25647 _25655.
Proof. exact (EQ_MP (@lem1108203 _25645 _25647 _25655) (@lem1108128 _25645 _25647 _25655)). Qed.
