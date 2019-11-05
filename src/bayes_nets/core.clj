(ns bayes-nets.core
    (:require [clojure.core.match :refer [match]]
              [clojure.pprint :refer [pprint]]
              [clojure.test :refer :all]))

(defn vectify [coll]
  (if (sequential? coll) (vec coll) coll))

(defn reduce-expr [expr]
  (match (vectify expr)
         false false
         true true
         ['| A B & more] (or (reduce-expr A)
                             (reduce-expr B)
                             (some reduce-expr more))
         ['& A B & more] (and (reduce-expr A)
                              (reduce-expr B)
                              (not-any? (complement reduce-expr) more))
         [_ true true] true
         ['& X false] false
         ['& false X] false
         ['| true X] true
         ['| X true] true
         ['=> false X] true
         ['& false X] false
         ['iff X Y] (or (and (reduce-expr X)
                             (reduce-expr Y))
                        (and (not (reduce-expr X)) (not (reduce-expr Y))))
         ['! X] (not (reduce-expr X))
         ['=> X Y] (or (not (reduce-expr X)) (reduce-expr Y))
         ['& X Y] (and (reduce-expr X) (reduce-expr Y))
         ['| X Y] (or (reduce-expr X) (reduce-expr Y))))

(defn negate [variable]
  (if (symbol? variable)
    (keyword variable)
    (symbol (name variable))))

(defn substitute-world [world e]
  (cond (sequential? e)
        (cons (first e) (map (partial substitute-world world) (next e)))

        (contains? world (keyword e))
        (let [v ((keyword e) world)]
          (if (keyword? e) v (not v)))

        :else
        (throw (Exception. "Ack! variable not in world"))))

(defn satisfies-world? [world expr]
  (reduce-expr (substitute-world world expr)))

(defn make-truth-table [[v & variables]]
  (if (nil? v) '(())
      (concat
       (for [ret (make-truth-table variables)]
         (cons (keyword v) ret))
       (for [ret (make-truth-table variables)]
         (cons (symbol v) ret)))))

(defn make-worlds [truth-table]
  (map (fn [variables]
         (into {}
               (map (fn [v] [(keyword v) (keyword? v)]))
               variables))
       truth-table))

(defn variables-of [expr]
  (cond (contains? (meta expr) :variables)
        (into #{} (map name) (-> expr meta :variables))

        (sequential? expr)
        (into #{} (mapcat variables-of) (next expr))

        (or (keyword? expr) (symbol? expr))
        (list (name expr))

        :else
        (throw (Exception. "Ack! Bad type in expression!" (type expr)))))

(defn valid? [sentence]
  (every? (fn [world]
            (reduce-expr (substitute-world world sentence)))
          (make-worlds (make-truth-table (seq (variables-of sentence))))))

(defn first-invalid [sentence]
  (first (remove (fn [world]
                   (reduce-expr (substitute-world world sentence)))
                 (make-worlds (make-truth-table (seq (variables-of sentence)))))))

(defn disagreements [s1 s2]
  (filter (fn [world]
            (not= (reduce-expr (substitute-world world s1)) 
                  (reduce-expr (substitute-world world s2))))
          (make-worlds (make-truth-table (seq
                                          (into (variables-of s1)
                                                (variables-of s2)))))))

(defn agree? [s1 s2]
  (empty? (disagreements s1 s2)))

(defprotocol IPdf
  (P [this]))

(defprotocol IWorld)

(defn world? [x]
  (or (satisfies? IWorld x) (map? x)))

(defn sentence? [x]
  (sequential? x))

(defn implies? [world s1 s2]
  (or (not (reduce-expr (substitute-world world s1)))
      (reduce-expr (substitute-world world s2))))

(defn counter-examples [pred s1 s2]
  (remove #(pred % s1 s2)
          (make-worlds (make-truth-table (seq (into (variables-of s1)
                                                    (variables-of s2)))))))

(defn for-all-worlds? [pred & sentences]
  (every? #(apply pred % sentences)
          (make-worlds (make-truth-table
                        (seq
                         (into #{}
                               (mapcat variables-of)
                               sentences))))))

(defn |=
  {:doc "take (|= w a) to mean that a sentence
a is true at world w. Equivalently, we say that w satisfies
(or entails) sentence a."}
  [w a]
  (cond (world? w) (reduce-expr (substitute-world w a))
        (sentence? w) (implies? w a)
        :else (throw (Exception. "Ack! wft is w?"))))

(defn Mods
  ([alpha] (Mods alpha (variables-of alpha)))
  ([alpha variables]
   (filter (fn [world]
             (|= world alpha))
           (make-worlds (make-truth-table (seq variables))))))

(defmacro exists [generator-form test-expr iterations]
  `(loop [cnt# ~iterations ~@generator-form]
     (and (pos? cnt#)
          (or ~test-expr (recur (dec cnt#) ~@(take-nth 2 (next generator-form)))))))

(defmacro for-all [generator-form test-expr iterations]
  `(loop [cnt# ~iterations ~@generator-form]
     (or (zero? cnt#)
         (and ~test-expr (recur (dec cnt#) ~@(take-nth 2 (next generator-form)))))))

(defn make-variable-set [n]
  (take n (iterate (comp symbol str char inc int first name) 'A)))

(defn a-sentence [variables s]
  (let [operators ['=> '| '& '!]
        gen-sent (fn gen-sent [size]
                   (if (or (zero? size)
                           (= (rand-int 5) 1))
                     (rand-nth variables)
                     (let [op (rand-nth operators)
                           args (list (gen-sent (dec size))
                                      (gen-sent (dec size)))]
                       (cons op
                             (case op
                               ! (list (gen-sent (dec size)))
                               (list (gen-sent (dec size))
                                     (gen-sent (dec size))))))))]
    (gen-sent s)))

(defn a-world [variables]
  (into {}
        (map (fn [v] [v (rand-nth [true false])]))
        variables))

(defn inconsistent? [expr]
  (empty? (Mods expr)))

(defn consistent? [expr]
  (not (inconsistent? expr)))

(defn equivalent? [s1 s2]
  (let [vars (into (variables-of s1)
                   (variables-of s2))]
    (= (Mods s1 vars)
       (Mods s2 vars))))

(def expr-a '[& (=> :A :B) (=> :A B)])
(def expr-b '[=> (| :A :B) (& A B)])

(def world {:A false :B false})
(assert (= (satisfies-world? world expr-a) true))

(def expr-a '[=> [& :A [=> :A :B]] :B])
(= (valid? expr-a) true)

(def expr-b '(| (& :A :B) (& :A B)))
(= (valid? expr-b) false)
(first-invalid expr-b)

(def expr-c '(=> (=> :A :B) (=> A B)))
(assert (= (valid? expr-c) false)) 
(first-invalid expr-b)

(deftest e2.3-a
  (let [expr1 '(=> :A :B)
        expr2 '(=> :B :A)]
    (is (= (agree? expr1 expr2) false))
    (is (= (first (disagreements expr1 expr2))
           {"A" false "B" true}))))

(deftest e2.3-b
  (let [expr1 '(& (=> :A :B) (=> :A B))
        expr2 'A]
    (is (= (agree? expr1 expr2) true))))

(deftest e2.3-c
  (let [expr1 '(=> A B)
        expr2 '(& (| :A B :C)
                  (| :A B C))]
    (is (= (agree? expr1 expr2) false))
    (is (= (first (disagreements expr1 expr2))
           {"A" false "B" true "C" true}))))

(ns bayes-nets.book)

(deftest e2.4-a
  (let [expr1 '(& (=> :A :B) B)
        expr2 :A]
    (is (= (for-all-worlds? implies? expr1 expr2) false))
    (is (= (first (counter-examples implies? expr1 expr2))
           {"A" false "B" false}))))

(deftest e2.4-b
  (let [expr1 '(& (| :A B) :B)
        expr2 :A]
    (is (= (for-all-worlds? implies? expr1 expr2) true))))

(deftest e2.4-c
  (let [expr1 '(& (| :A :B) (| :A B))
        expr2 :A]
    (is (= (for-all-worlds? implies? expr1 expr2) true))))
;; *** 2.5
;;   Which of the following pairs of sentences are mutually exclusive?
;;   Which are exhaustive? If a pair of sentences is not mutually exclusive,
;;   identify a world at which they both hold. If a pair of sentences is not
;;   exhaustive, identify a world in which neither holds.
(ns bayes-nets.book)

(defn mutually-exclusive?
  ([worlds s1 s2 & more]
   (every? (partial apply mutually-exclusive? worlds)
           (for [a      (list* s1 s2 more)
                 b      (list* s1 s2 more)
                 :while (not (identical? a b))]
             [a b])))
  ([worlds s1 s2]
  (every? (fn [world]
             (not= (reduce-expr (substitute-world world s1))
                   (reduce-expr (substitute-world world s2))))
           worlds))
  ([s1 s2]
   (mutually-exclusive? (make-worlds (make-truth-table (seq
                                                        (into (variables-of s1)
                                                              (variables-of s2)))))

                        s1
                        s2)))


(defn first-inclusion [s1 s2]
  (first
   (remove (fn [world]
             (not= (reduce-expr (substitute-world world s1))
                   (reduce-expr (substitute-world world s2))))
           (make-worlds (make-truth-table (seq
                                           (into (variables-of s1)
                                                 (variables-of s2))))))))


(defn exhaustive?
  ([worlds s1 s2 & more]
   (every? (partial apply mutually-exclusive? worlds)
           (for [a (list* s1 s2 more)
                 b (list* s1 s2 more)
                 :while (not (identical? a b))]
             [a b])))
  ([worlds s1 s2]
   (every? (fn [world]
             (or (reduce-expr (substitute-world world s1))
                 (reduce-expr (substitute-world world s2))))
           worlds))
  ([s1 s2]
   (exhaustive? (make-worlds (make-truth-table (seq
                                                (into (variables-of s1)
                                                      (variables-of s2)))))
                s1 s2)))


(deftest e2-5-a
  (let [expr-a '(| :A :B)
        expr-b '(| A B)]
    (is (= false true))
    (is (= (mutually-exclusive? expr-a expr-b) false))
    (is (= (first-inclusion expr-a expr-b)
           {"B" true "A" false}))
    (is (= (exhaustive? expr-a expr-b) true))))


(deftest e2.5-b
  (let [expr-a '(| :A :B)
        expr-b '(& A B)]
    (is (= (mutually-exclusive? expr-a expr-b) true))
    (is (= (exhaustive? expr-a expr-b) true))))


(deftest e2.5-c
  (let [expr-a :A
        expr-b '(& (| A :B) (| A B))]
    (is (= (mutually-exclusive? expr-a expr-b) true))
    (is (= (exhaustive? expr-a expr-b) true))))

(ns bayes-nets.book)

(deftest e2.6
    "To prove the refutation theorem it suffices to show
  that there exsts sentences alpha and beta such that it is not
  the case that iff alpha |= beta, alpha && ^beta is consistent"
    (for-all [variables (make-variable-set 3)
              alpha (a-sentence variables 3)
              beta (a-sentence variables 3)]
             (inconsistent? ['iff ['=> alpha beta]
                                  ['& alpha ['! beta]]])
             50))

(deftest e2.7
  "Provides numerical evidence for the deduction theorem"
  (is (for-all [variables (make-variable-set 3)
                alpha (a-sentence variables 3)
                beta (a-sentence variables 3)]
               (valid? ['iff ['=> alpha beta]
                             ['=> alpha beta]])
               500)))

(deftest e2.8
  (is (for-all [variables (make-variable-set 5)
                alpha (a-sentence variables 7)
                beta (a-sentence variables 7)]
               (equivalent? alpha ['=> ['=> alpha beta]
                                       ['& alpha beta]])
               150)))

(deftest e2.9
  (is (for-all [variables (make-variable-set 5)
                alpha (a-sentence variables 7)
                beta (a-sentence variables 7)]
               (equivalent? beta ['iff ['=> alpha beta]
                                       ['| alpha beta]])
                   250)))

(defn to-cnf [expr])

(deftest e2.10-a
  (let [expr '(=> :P (=> :Q :R))]
    (is (= (to-cnf expr)
           "..."))))

(deftest e2.10-b
  (let [expr '(! (& (=> P Q) (=> R S)))]
    (is (= (to-cnf expr)
               "..."))))

(ns bayes-nets.book
  (:require [clojure.set :as s]))

(defn decomposable?
  {:doc "An NNF circuit is decomposable if each
of its and-nodes atisfies the property: For each pair
of children C1 and C2 of the and-node, the sentence
represented by C1 and C2 cannot share variables."}
  [circuit]
  (match (vectify circuit)
         ['& C1 C2] (empty? (s/intersection
                             (variables-of C1)
                             (variables-of C2)))
         ['| C1 C2] (and (decomposable? C1)
                         (decomposable? C2))))

(defn deterministic?
  {:doc "An NNF circuit is deterministic if each of its
or-nodes satisfies the following property: For each pair
of children C1 and C2 of the or-node,
the sentence represented by C1 and C2 must be mutually
exclusive."}
  [circuit]
  (match (vectify circuit)
         ['& C1 C2] (and (deterministic? C1)
                         (deterministic? C2))
         ['| C1 C2] (mutually-exclusive? C1 C2)))

(defn smooth?
  {:doc "A NNF circuit is smooth if each of its or-nodes
satisfies the following proerty: For each pair of children C1
and C2 of the or-node the sentences represented by C1 and C2
must mention the same set of variables."}
  [circuit]
  (match (vectify circuit)
         ['| C1 C2] (= (variables-of C1)
                       (variables-of C2))
         ['& C1 C2] (and (smooth? C1)
                         (smooth? C2))))

(defn augment
  {:doc "Takes a decomposable and deterministic circuit
and augments it to be also smooth."}
  [circuit])

#_(for-all [X (a-nnf {:decomposable? true})
            Y (a-cnf X)]
           (smooth? Y))

(defprotocol IProb
  (Prob [this worlds]))

(defn Pr
  ([alpha]
   (cond (sentence? alpha)
         (Pr alpha (make-worlds (make-truth-table (seq (variables-of alpha)))))

         (world? alpha)
         (.Probability alpha)))
  ([alpha worlds]
   (if (satisfies? IProb alpha)
     (.Prob alpha worlds)
     (transduce (comp (filter #(satisfies-world? % alpha))
                      (map :Probability))
                +
                worlds))))

(defprotocol IEntails
  (entailed? [this world]))

(defn entails?
  ([w x]
   (cond (keyword? x) (x w)
         (symbol? x) (not ((keyword x) w))
         (satisfies? IEntails x) (entailed? x w)
         :else ; legacy
         (satisfies-world? w x)))
  ([w x worlds]
   {:pre [(sentence? w)]}
   (implies? w x worlds)))

(defn update-belief [worlds evidence]
  (into (empty worlds) 
        (map (fn [world]
               (if (entails? world evidence)
                 (assoc world :Probability (/ (Pr world) (Pr evidence worlds)))
                 (assoc world :Probability 0))))
        worlds))

;; *** Utils

(defn rat [op & args]
  (apply op (map rationalize args)))

(deftype GIVEN [X Y]
  IProb
  (Prob [this worlds]
   (Pr X (update-belief worlds Y))))


(defn combs [n k]
  (cond (= n k) (list (range n))
        (= k 1) (map list (range n))
        :else
        (concat (map (partial cons (dec n))
                     (combs (dec n) (dec k)))
                (combs (dec n) k))))


(defn Given [X Y] (GIVEN. X Y))

(defprotocol IEntropy
  (entropy [this worlds]))

(defn log2 [n]
  (/ (Math/log n) (Math/log 2)))

(declare Equal)


(defn values-of [variable worlds]
  (let [k (keyword variable)]
    (for [value (-> worlds meta :slots k :range)]
      (if (instance? Boolean value)
        (if (true? value) k (symbol variable))
        (Equal k value)))))


(defn ENT
  {:doc "Weird definition of entropy that currently only works for boolean
   variables."}
  ([X]
   (ENT X (make-worlds (make-truth-table (seq (variables-of X))))))
  ([X worlds]
   (if (satisfies? IEntropy X)
     (entropy X worlds)
     (- (transduce (map (fn [x]
                          (* (Pr x worlds)
                             (log2 (Pr x worlds)))))
                   +
                   (values-of X worlds))))))


(defmacro defpdf [name fields]
  (let [record (symbol (str name "_" (gensym)))
        metadata (into {} (map (fn [f] [(keyword f) (meta f)])) fields)]
    (println "metadata" metadata)
    `(do (defrecord ~record ~(conj fields 'Probability) IPdf IWorld)
         (defn ~name [tb#]
           (with-meta
             (set (for [row# (into [] (partition-all ~(inc (count fields))) tb#)]
                    (apply ~(symbol (str "->" record)) (conj (pop row#)
                                                             (rationalize (peek row#)))))) 
             {:slots ~metadata})))))


(defpdf MyPdf [^{:range [true false]} Earthquake
               ^{:range [true false]} Burglary
               ^{:range [true false]} Alarm])
(def tb-3-1
  (MyPdf [true  true  true  0.0190
          true  true  false 0.0010
          true  false true  0.0560
          true  false false 0.0240
          false true  true  0.1620
          false true  false 0.0180
          false false true  0.0072
          false false false 0.7128]))

(defn about= [x y]
  (let [epsilon 0.02]
    (< (Math/abs (- x y))
       epsilon)))

(assert (about= (ENT "Earthquake" tb-3-1) 0.469))
(assert (about= (ENT "Burglary" tb-3-1) 0.722))
(assert (about= (ENT "Alarm" tb-3-1) 0.802))

(defn temp [X y worlds]
  (- (transduce (map (fn [x]
                       (* (Pr (Given x y) worlds)
                          (log2 (Pr (Given x y) worlds)))))
                +
                (values-of X worlds))))

(deftype X-Given-y [X y]
  IEntropy
  (entropy [this worlds]
    (temp X y worlds)))

(deftype X-Given-Y [X Y]
  IEntropy
  (entropy [this worlds]
    (transduce (map (fn [y]
                      (*  (Pr y worlds) (ENT (X-Given-y. X y) worlds))))
               +
               (values-of Y worlds))))

;; Note conditioning X on Y results in an entropy decrease.
(assert (about= (ENT (X-Given-y. "Burglary" :Alarm) tb-3-1) 0.8249366167586))
(assert (about= (ENT (X-Given-y. "Burglary" 'Alarm) tb-3-1)  0.16939463925045634))
(assert (about= (ENT (X-Given-Y. "Burglary" "Alarm") tb-3-1)  0.32947799015795315))

(assert (= (Pr :Earthquake tb-3-1)
           (Pr (Given :Earthquake :Burglary) tb-3-1)))

(defn independent? [alpha beta worlds]
  (= (* (Pr alpha worlds)
        (Pr beta worlds))
     (Pr ['& alpha beta] worlds)))

(assert (independent? :Earthquake :Burglary tb-3-1))

(assert (= (Pr :Burglary tb-3-1)
           (Pr (Given :Burglary :Earthquake) tb-3-1)))
(assert (independent? :Burglary :Earthquake tb-3-1))

(defn disjoint? [alpha beta variables]
  (empty? (clojure.set/intersection
           (set (Mods alpha variables))
           (set (Mods beta variables)))))

(defmacro defproperty [& args] nil)
(defproperty ConditionalIndependence
  (= (Pr ['& alpha beta]) (* (Pr alpha) (Pr beta))))

;; re-def probability to use entails?
(defn Pr
  ([alpha]
   (cond (sentence? alpha)
         (Pr alpha (make-worlds (make-truth-table (seq (variables-of alpha)))))

         (world? alpha)
         (.Probability alpha)))
  ([alpha worlds]
   (if (satisfies? IProb alpha)
     (.Prob alpha worlds)
     (transduce (comp (filter #(entails? % alpha))
                             (map :Probability))
                +
                worlds))))



(defpdf TB-3-3 [^{:range [:normal :extreme]} Temp
                ^{:range [:normal :extreme]} Sensor1
                ^{:range [:normal :extreme]} Sensor2])
(def tb-3-3
  (TB-3-3 [:normal  :normal  :normal  0.567
           :normal  :normal  :extreme 0.144
           :normal  :extreme :normal  0.064
           :normal  :extreme :extreme 0.016
           :extreme :normal  :normal  0.008
           :extreme :normal  :extreme 0.032
           :extreme :extreme :normal  0.032
           :extreme :extreme :extreme 0.128]))


(defmacro deflogic [name fields & specs]
  `(defrecord ~name ~fields
     ~@specs))


(deflogic EQUAL [variable value]
  IEntails
  (entailed? [this world]
    (= (variable world) value)))


(deflogic OR [X Y]
  IEntails
  (entailed? [this world]
    (or (entails? world X)
        (entails? world Y))))


(deflogic AND [X Y]
  IEntails
  (entailed? [this world]
    (and (entails? world X)
         (entails? world Y))))


(deflogic GIVEN [X Y]
  IEntails
  (entailed? [this world]
    (or (not (entails? world X))
        (entails? world Y)))
  IProb
  (Prob [this worlds]
        (Pr X (update-belief worlds Y))))


(deflogic NOT [X]
  IEntails
  (entailed? [this world]
    (not (entails? world X))))


(defn Equal [variable value]
  (EQUAL. variable value))


(defn And
  ([X Y]
   (AND. X Y))
  ([X Y Z]
   (AND. X (AND. Y Z)))
  ([X Y Z & more]
   (reduce And (And X Y Z) more)))


(defn Or
  ([X Y]
   (OR. X Y))
  ([X Y Z]
   (OR. X (OR. Y Z)))
  ([X Y Z & more]
   (reduce Or (Or X Y Z) more)))


(defn Given
  ([X Y]
   (GIVEN. X Y)))


(defn Not [X] (NOT. X))



#_(assert (= (flatten (And :A (Or :B (Not :C)))) 
             `(AND :A OR :B NOT :C)))

(assert (= (seq (eval `(Or :A :B)))
           (seq (Or :A :B))))


(assert (= (And :A (Or :B :C)) 
           (And :A (Or :B :C))))


(assert (= (Pr '[& :Burglary :Alarm] tb-3-1) ; old method
           (Pr (And :Burglary :Alarm) tb-3-1) ; new method
           181/1000))


(assert (= (Pr '[| :Burglary :Alarm] tb-3-1) 
           (Pr (Or :Burglary :Alarm) tb-3-1)
           329/1250))


(assert (= (Pr (Not :Burglary) tb-3-1)
           (Pr '[! :Burglary] tb-3-1)
           4/5))


(assert (about= (ENT (X-Given-Y. "Burglary" "Alarm") tb-3-1) 0.328))
(assert (about= (ENT (X-Given-y. "Temp" (Equal :Sensor2 :normal)) tb-3-3) 0.325))

(assert (about= (Pr (Equal :Temp :normal) tb-3-3) 0.80))

(assert (= (Pr (Equal :Temp :normal) tb-3-3) 791/1000))
(assert (= (Pr (Equal :Sensor1 :normal) tb-3-3) 751/1000))
(assert (= (Pr (Equal :Sensor2 :normal) tb-3-3) 671/1000))

(assert (about= (Pr (Given (Equal :Sensor2 :normal) (Equal :Sensor1 :normal)) tb-3-3) 0.768))

;; Something is severely screwed up with this example.
#_(assert (= (Pr (Given (Equal :Sensor2 :normal) (Equal :Temp :normal))
               tb-3-3) 
           (Pr (And (Given (Equal :Sensor2 :normal)
                           (Equal :Temp :normal))
                    (Equal :Sensor1 :normal))
               tb-3-3)))


(defn conditionally-indepedent? [alpha beta zeta worlds]
  (or (zero? (Pr (Given alpha zeta) worlds))
      (= (Pr (Given alpha (And beta zeta)) worlds)
         (Pr (Given alpha zeta) worlds))))

(defn conditionally-indepedent? [alpha beta zeta worlds]
  (or (zero? (Pr zeta worlds))
      (= (Pr (Given (And alpha beta) zeta) worlds)
         (* (Pr (Given alpha zeta) worlds)
            (Pr (Given alpha beta) worlds)))))

(defn MI [X Y worlds]
  (transduce (map (fn [[x y]]
                    (* (Pr (And x y) worlds)
                       (log2 (/ (Pr (And x y) worlds)
                                (* (Pr x worlds)
                                   (Pr y worlds)))))))
             +
             (for [x (values-of X worlds)
                   y (values-of Y worlds)]
               [x y])))


(assert (about= (ENT "Burglary" tb-3-1) 0.7219))
(assert (about= (MI "Burglary" "Alarm" tb-3-1) 0.3924))

(assert (= (MI "Burglary" "Earthquake" tb-3-1) 0.0))
(assert (and (= (Pr (Given :Burglary :Earthquake) tb-3-1)
                (Pr :Burglary tb-3-1))
             (= (Pr (Given :Earthquake :Burglary) tb-3-1) 
                (Pr :Earthquake tb-3-1))))

(assert (and (= (ENT "Burglary" tb-3-1)
                (ENT (X-Given-Y. "Burglary" "Earthquake") tb-3-1)) 
             (= (ENT "Earthquake" tb-3-1)
                (ENT (X-Given-Y. "Earthquake" "Burglary") tb-3-1))))

(defrecord VaraiableSet [variables]
  IProb
  (Prob [this worlds]
    (- (transduce (map (fn [var]
                         (* (Pr var worlds) ; Pr(variable) is never defined!!!!!
                            (log2 (Pr var worlds)))))
                  +
                  variables))))

(assert (= (Pr (And :Alarm :Burglary :Earthquake) tb-3-1) 
           (* (Pr (Given :Alarm (And :Burglary :Earthquake)) tb-3-1) 
              (Pr (Given :Burglary :Earthquake) tb-3-1) 
              (Pr :Earthquake tb-3-1)) 
           19/1000))

(defpdf UrnExample [^{:range [:Black :White]} Color
                    ^{:range [:A :B]} Urn])
(def urn-example
  (UrnExample [:Black :A 1/6
               :Black :B 1/8
               :White :A 2/6
               :White :B 3/8]))

(assert (= (Pr (Equal :Urn :A) urn-example) 1/2))
(assert (= (Pr (Equal :Urn :B) urn-example) 1/2))
(assert (= (Pr (Equal :Color :White) urn-example) 17/24))
(assert (= (Pr (Equal :Color :Black) urn-example) 7/24))
(assert (= (+ 17/24 7/24) 1))
(assert (= (Pr (Given (Equal :Color :White) (Equal :Urn :A)) urn-example) 2/3))

(let [A (Equal :Urn :A)
      B (Equal :Color :White)]
  (assert (= (Pr (And B A) urn-example) 
             (* (Pr (Given B A) urn-example)
                (Pr A urn-example))
             (* (Pr (Given A B) urn-example) ; notice symmetry
                (Pr B urn-example)))))

(defn chain
  ([w A] (Pr A w))
  ([w A B] (* (Pr (Given A B) w) (chain w B)))
  ([w A B & variables]
   (* (Pr (Given A (apply And B variables)) w)
      (apply chain w B variables))))


(= (chain tb-3-1 :Burglary :Earthquake :Alarm) 
   (Pr (And :Burglary :Earthquake :Alarm) tb-3-1))

;; We can do it symbolically as well:


(defn symbolic-chain
  ([[op [And X Y & Vars] worlds]]
   (if (nil? Y)
     `(Pr ~X ~worlds)
     `(* (Pr (Given ~X (And ~Y ~@Vars)) ~worlds)
         ~(symbolic-chain [op (list* `And Y Vars) worlds])))))


;; We'll want to simplify the symbolic expression as
;; seprate step:

(defn simplify [expr]
  (let [expr (vectify expr)]
    (match expr
      [And X] X
      [Or X] X
      [(:or `* `+ `/ `-) & xs]
      `[~(first expr)
        ~@(mapcat (fn [x]
                    (let [e (simplify x)
                          op (first expr)]
                      (match e
                        [op & ys] ys
                        :else (vector e))))
                  xs)]
      [& expr] (mapv simplify expr)
      :else expr)))

(assert (= (simplify `[* [And [* :A :B]]  [* :C [/ :D [* :E  [* :F :G]]]]]) 
           `[* :A :B :C [/ :D [* :E :F :G]]]))

(assert (= (simplify `[+ [And [+ :A :B]]  [+ :C [/ :D [- :E  [- :F :G]]]]])
           `[+ :A :B :C [/ :D [- :E :F :G]]]))


(assert (= (simplify (symbolic-chain `(Pr (And A B) *worlds*))) 
           (simplify `(* (Pr (Given A B) *worlds*) (Pr B *worlds*)))))


(defn make-uniform-pdf [worlds]
  "Randomly assign a probability to each world
   such that the total probability sums to 1.
   We can do successively cutting the space
   between zero and one at random places. Then
   the distance from the nth cut to the n-1th cut
   is the Probability of the nth world." 
  (let [cuts (sort (list* 0.0 1.0 (take (dec (count worlds)) (repeatedly rand))))
        probs (map - (next cuts) cuts)]
    (map (fn [world prob]
           (assoc world :Probability prob))
         worlds
         probs)))



(comment Law of Total Probability
  "It proves to be prohibitively dificult to find alpha and Betas by random search that
   satisfy mutual exclusivity and exhaustivity. But this expression should evaluate
   to true for the rest of time."
  (for-all [variables (make-variable-set 3)
            alpha (a-sentence variables)
            worlds (make-uniform-pdf (make-worlds (make-truth-table variables)))
            betas (take (rand-int 4)
                        (filter (fn [events]
                                  (and (apply mutually-exclusive? worlds alpha events)
                                       (apply exhaustive? worlds alpha events)))
                                (take (rand-int 3)
                                      (repeatedly (partial a-sentence variables 3)))))]
           (= (Pr alpha world)
              (transduce (map (fn [b]
                                (Pr (comment :A) (And alpha b) worlds))) 
                         +
                         betas))))

(defmacro rule [& args] nil)
(rule '(= (Pr alpha *worlds*)
          (+ (Pr (And alpha beta) *worlds*)
             (Pr (And alpha (Not beta)) *worlds*))))
(rule '(= (Pr alpha *worlds*)
          (+ (Pr (* (Pr (Given alpha beta) *worlds*)
                    (Pr beta *worlds*)))
             (Pr (* (Pr (Given alpha (Not beta)) *worlds*)
                    (Pr 'beta *worlds*))))))

(rule bayes-rule [alpha (a-sentence)
                  beta (a-sentence)]
      (= (Pr (Given alpha beta) *worlds*)
         (/ (* (Pr (Given beta alpha) *worlds*)
               (Pr alpha *worlds*))
            (Pr beta *worlds*))))

(rule [alpha (a-sentence)
       beta (a-sentence)]
      (= (* (Pr (Given alpha beta) *worlds*)
            (Pr beta *worlds*))
         (* (Pr (Given beta alpha) *worlds*)
            (Pr alpha *worlds*))))


(rule [alpha (a-sentence)
       beta (a-sentence)]
      (= (Pr (And alpha beta) *worlds*)
         (Pr (And beta alpha) *worlds*)))

(defpdf BayesExample [^{:range [:sick :fine]} Patient
                      ^{:range [:pos :neg]} Result])

(def bayes-example
  (BayesExample [:sick :pos (* 1/1000   95/100)  ;; correct-positive
                 :sick :neg (* 1/1000   5/100)   ;; false-negative
                 :fine :pos (* 999/1000 2/100)   ;; false-positive.
                 :fine :neg (* 999/1000 98/100)  ;; correct-negative.
                 ]))

(def Is Equal)

(assert (= (Pr (Given (Is :Patient :sick)
                      (Is :Result :pos))
               bayes-example)
           95/2093))

(defn Mods-2
  ([alpha] (Mods alpha (variables-of alpha)))
  ([alpha worlds]
   (filter (fn [world]
             (|= world alpha))
           worlds)))

(defn entails-2?
  "support an operation on sentences."
  [w b worlds]
  (= (set (Mods-2 w worlds))
     (clojure.set/union (set (Mods-2 w worlds))
                        (set (Mods-2 b worlds)))))


(defn Pr*1
  {:doc "A very strange and bad way to express asigning belief `q` to `beta`
and updating belief state. Or like updating belief under the assigment of `beta`
to `q`. Or like what alpha would be if beta we assign q to beta."}
  ([alpha beta q worlds]
   (if (entails-2? alpha beta worlds)
     (* (/ q (Pr beta worlds))
        (Pr alpha worlds))
     (* (/ (- 1 q) (Pr (Not beta) worlds))
        (Pr alpha worlds)))))

(assert (= (Pr*1 :Burglary :Alarm (Pr :Alarm tb-3-1) tb-3-1) 
           (Pr :Burglary tb-3-1))) 
(assert (= (Pr*1 :Alarm :Alarm 1/2 tb-3-1) 1/2)) 

(defn Pr*2 [a b q worlds]
  (+ (* q (Pr (Given a b) worlds))
     (* (- 1 q) (Pr (Given a (Not b)) worlds))))

(assert (= (Pr*1 :Burglary :Alarm (Pr :Alarm tb-3-1) tb-3-1) 
           (Pr*2 :Burglary :Alarm (Pr :Alarm tb-3-1) tb-3-1)))

(defn Pr*3 [alpha B Q worlds]
  (transduce (map (fn [[b q]]
                    (* q (Pr (Given alpha b) worlds))))
             +
             (map vector B Q)))
(defn Pr*5
  ([worlds a b q]
   (* q (Pr (Given a b) worlds)))
  ([worlds a b1 q1 b2 q2]
   (+ (Pr*5 worlds a b1 q1)
      (Pr*5 worlds a b2 q2)))
  ([worlds a b1 q1 b2 q2 & args]
   (+ (Pr*5 worlds a b1 q1 b2 q2)
      (apply Pr*5 args))))


(defpdf Jeffrey [^{:range [:sold :unsold]} Cloth
                 ^{:range [:green :blue :violet]} Color])
(def cloth-example
  (Jeffrey [:sold   :green  3/25
            :unsold :green  9/50
            :sold   :blue   3/25
            :unsold :blue   9/50
            :sold   :violet 8/25
            :unsold :violet 2/25]))


(assert (= (Pr*3 (Is :Cloth :sold)
                 [(Is :Color :green) (Is :Color :blue) (Is :Color :violet)]
                 [7/10 1/4 1/20]
                 cloth-example) 
           21/50))


(defn Pr*4 [b q worlds] 
  (into (empty worlds)
        (map (fn [world]
               (if (entails? world b)
                 (assoc world :Probability (* (/ q (Pr b worlds))
                                              (:Probability world)))
                 (assoc world :Probability (* (/ (- 1 q) (Pr (Not b) worlds))
                                              (:Probability world))))))
        worlds))

;; Groking the nutballs notation

(assert (= (Pr*2 :Burglary :Alarm 3/4 tb-3-1) 
           (Pr :Burglary (Pr*4 :Alarm 3/4 tb-3-1)) 
           (Pr*3 :Burglary [:Alarm 'Alarm] [3/4 1/4] tb-3-1))) 


(assert (about= (Pr (Is :Cloth :sold)
                    (Pr*4 (Is :Color :violet) 0.05
                          (Pr*4 (Is :Color :blue) 0.25
                                (Pr*4 (Is :Color :green) 0.7 cloth-example)))) 
                0.42))


(defn Odds [worlds event]
  (/ (Pr event worlds)
     (Pr (Not event) worlds)))

(assert (= (Odds tb-3-1 :Burglary) 1/4))

(assert (= (Pr :Burglary tb-3-1) 1/5))

(defn bayes-factor [worlds a b q]
  (/ (Odds (Pr*4 b q worlds) a)
     (Odds worlds a)))

(assert (= (bayes-factor tb-3-1 :Burglary :Alarm 1/2) 1767995/711541))

(comment 
  (for-all [worlds (a-worlds)
            event (a-sentence)
            evidence (rand)
            k (rand-int 4)]
           (= (Pr*2 event worlds)
              (/ (* k (Pr event worlds))
                 (+ (* k (Pr event worlds))
                    (Pr event worlds))))))

(defpdf HouseExample [Alarm Burglary])

(def house-example
  (HouseExample [true  true   19/200000
                 true  false  9999/1000000
                 false true   1/200000
                 false false  989901/1000000]))

(assert (= (transduce (map :Probability) + house-example) 1))

(assert (= (let [a :Burglary ;; Event we're 'measuring'
                 b :Alarm    ;; Event that the evidence pertains to
                 k 4]        ;; Evidence factor
             (/ (+ (* k(Pr (And a b) house-example))
                   (Pr (And a (Not b)) house-example))
                (+ (* k (Pr b house-example))
                   (Pr (Not b) house-example))))
           35/93662))

(defn update-with-bayes-factor [worlds measurement event k]
  (/ (+ (* k (Pr (And measurement event) worlds)) 
        (Pr (And measurement (Not event)) worlds)) 
     (+ (* k (Pr event worlds))
        (Pr (Not event) worlds))))

(assert (= (update-with-bayes-factor house-example :Burglary :Alarm 4)
           35/93662))

(assert (= (Pr :Burglary house-example) 
           (update-with-bayes-factor house-example :Burglary :Alarm 1)))

(assert (= (update-with-bayes-factor house-example :Burglary :Alarm 0) 
           (Pr (Given :Burglary (Not :Alarm)) house-example)))


(defpdf MurderExample [^{:range [:david :dick :jane]} Killer])
(def ricks-belief
  (MurderExample [:david 2/3
                  :dick  1/6
                  :jane  1/6]))


(assert (= (transduce (map :Probability) + ricks-belief) 1))
;; According to Rich, the odds of David being the killer is 2

(assert (= (Odds ricks-belief (Is :Killer :david)) 2))

(assert (= (update-with-bayes-factor ricks-belief
                                     (Is :Killer :david)
                                     (Is :Killer :david)
                                     3)
           6/7))

(assert (= (Pr*2 (Is :Killer :david) (Is :Killer :david) 6/7 ricks-belief)
           6/7))

(def jons-belief
  (MurderExample [:david 1/2
                  :dick  1/4
                  :jane  1/4]))

(assert (= (update-with-bayes-factor jons-belief
                                     (Is :Killer :david)
                                     (Is :Killer :david)
                                     3)
           3/4))

;; need to revisit this
(assert (let [false-positive-rate 2/100
              false-negative-rate 5/100]
          (= (*  (Odds bayes-example (Is :Patient :sick))))
          (* (/ (- 1 false-negative-rate)
                false-positive-rate)
             (Odds bayes-example (Is :Patient :sick)))))
