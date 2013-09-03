(ns solitaire.core
  (:require clojure.edn
            [clojure.algo.monads :as m]
            [clojure.tools.macro :as macro]))

(defmethod print-method clojure.lang.PersistentQueue [q w] (print-method '<- w) (print-method (seq q) w) (print-method '-< w))

(def red #{:hearts :diamonds :d :h})

(defn red? [suit] (boolean (red suit)))

(def black? (complement red?))

(defn named [i]
  (if (nil? i)
    "empty space"
    (-> i name clojure.string/capitalize)))

(defn to-s [[rank suit]]
  (->> [(if (nil? rank) "an" "the") ({11 "Jack" 12 "Queen" 13 "King" 1 "Ace"} rank rank)
        (if-not (nil? rank) "of") ({:h "Hearts" :d "Diamonds" :s "Spades" :c "Clubs"} suit (named suit))]
       (remove nil?)
       (clojure.string/join " ")))

(defn card-range
  ([suit end] (card-range suit 1 end))
  ([suit] (card-range suit 13))
  ([suit begin end]
     (->> (range begin (inc end))
          (map #(vector % suit))
          vec)))

(defmacro ->cond [& args]
  (let [[body expr] (-> args count dec (split-at args))]
   `(cond-> ~@expr ~@body)))

(defn take-first [coll]
  (->> coll (drop-while nil?) (take 1)))

(defn peek-pop
  ([stack]
     [(peek stack) (if (seq stack) (pop stack))])
  ([stack n]
     (loop [x n
            result [[] stack]]
       (let [[_ stack] result]
         (if-let [next-item (and (> x 0) (peek stack))]
           (recur (dec x)
                  (-> result
                      (update-in [0] conj next-item)
                      (update-in [1] pop)))
           result)))))

(defn valid-card? [[rank suit :as card]]
            (and (seq card) (= (count card) 2)
                 rank (number? rank) (<= rank 13) (> rank 0)
                 (or (red? suit) (#{:c :s :clubs :spades} suit))))

(defn card [[rank suit]]
  [rank (keyword suit)])

(defn normalize [{:keys [stock foundation tableau]}]
  "Internal representation:
     :f Foundation: up to four sequences of cards
     :tableau a sequence of maps: {:h index of next hidden :s stack}
     :w Waste: a stack of cards
     :s Stock: a queue of cards
   Extra:
     :h Hidden Tableau: a sequence of up to seven (possibly nil) sequences of cards (possibly nil). Can
          be queried for cards, and remembered so that the user doens't need to repeatedly input the same
          card(s). The parameterized value in the state describes how the down-stacks are initalized."
  (letfn [(pad [n item coll]
            (->> (repeat item) (concat coll) (take n) vec))
          (cards [coll]
            (->> coll (partition 2) (map card)))]
    {:foundation (->> foundation (partition 2) (map (fn [[rank suit]] (card-range suit rank))) (pad 4 []))
     :tableau (->> tableau
                   (partition 2)
                   (map cards)
                   (map-indexed
                    (fn [index col]
                      {:stack (vec col) :hidden index}))
                   (pad 7 {:stack [] :hidden 0}))
     :waste []
     :stock (->> stock cards (into clojure.lang.PersistentQueue/EMPTY))}))

(defn parent-pred [[rank suit]]
  (fn [{parent-stack :stack}]
    (let [[parent-rank parent-suit] (peek parent-stack)]
      (and (= (red? parent-suit) (black? suit))
           (= parent-rank (inc rank))))))

(defn- get-history [state]
  (-> state meta :history reverse))

(defmacro update-fn [fn-name state src-desc ks & body]
  `(macro/macrolet [(~fn-name [[update-fn# & update-args#] & desc#]
                              `(-> ~'~state
                                  (~update-fn# ~'~ks ~@update-args#)
                                  (vary-meta update-in [:history] conj
                                             (clojure.string/join " " [~'~src-desc ~@desc#]))))]
                   ~@body))

(defmacro map-fn [fn-name new-state area update desc & body]
  `(macro/macrolet [(~fn-name [[index# element#] & mapped-body#]
                              `(fn [~index# ~element#]
                                 (update-fn ~'~update ~'~new-state ~'~desc
                                            (into [~'~area ~index#] (if (= ~'~area :tableau) [:stack]))
                                            ~@mapped-body#)))]
                   ~@body))

(defmacro destination [[map-fn-name area moved update-fn-name & post-processing] & body]
  `(fn [[~moved new-state# desc#] state#]
     (->> state#
          ~area
          (map-indexed
           (map-fn ~map-fn-name new-state# ~area ~update-fn-name desc#
                   ~@body))
          (->cond ~@post-processing ~@post-processing))))

(defmacro def-dest [name args & body]
  `(def ~name (destination ~args ~@body)))

(def-dest to-tableau 
  [foreach :tableau card accept]
  (let [parent? (parent-pred card)]
    (foreach [index column]
             (if (parent? column)
               (accept (update-in conj card) "to tableau column" (inc index))))))

(def-dest to-foundation
  [foreach :foundation [rank suit :as card] accept take-first]
  (let [ace? (= rank 1)
        [parent-rank? parent-suit?] (if ace? (repeat nil?)
                                        [#(= (dec rank) %) #(= suit %)])
        parent? (fn [[rank suit]] (and (parent-rank? rank) (parent-suit? suit)))]
    (foreach [index stack]
             (if (parent? (peek stack))
               (accept (update-in conj card) "to foundation column" (inc index))))))

(def-dest orphan-parent
  [foreach :tableau [top-card :as stack] accept]
  (let [parent? (parent-pred top-card)]
    (foreach [index column]
             (if (parent? column)
               (accept (update-in into stack) "to" (-> column :stack first to-s) "at column" (inc index))))))

(def-dest empty-tableau
  [foreach :tableau king-stack accept take-first]
  (foreach [index {:keys [stack hidden]}]
    (if (and (= hidden 0) (empty? stack))
      (accept (assoc-in king-stack) "to column" (inc index)))))

(defn waste-card [state]
  (letfn [(desc [card]
            (clojure.string/join " " ["moved" (to-s card) "from waste pile"]))
          (create-source [card state return-values]
            (conj return-values [card (update-in [:waste] pop) (desc card)]))
          (next-state [state]
            (let [[new-waste new-stock] (peek-pop state 3)]
              (if (empty? new-waste)
                (recur (update-in [:stock] into (state :waste)))
                (-> state
                    (update-in [:waste] into new-waste)
                    (assoc-in :stock new-stock)))))]
    (loop [{:keys [waste stock] :as state} state
           return []]
     (if-let [card (peek waste)]
       (if-not (-> (map first return) (contains? card))
         (recur (next-state state) (create-source card state return))
         return)
       (if (or (seq stock) (seq waste))
         (recur (next-state state) return))))))

(letfn [(move-type [& defns]
          (fn [state]
            (m/domonad (m/maybe-t m/sequence-m)
                       [[find-movable destinations] (partition 2 defns)
                        source (find-movable state)
                        move (destinations source state)]
                       move)))
        (orphan [{:keys [tableau] :as state}]
          (->> tableau
               (map-indexed
                (fn [index {[[rank] :as stack] :stack}]
                  (if (and rank (not= rank 13))
                    [stack (assoc-in state [:tableau index :stack] [])
                     (str "Moved orphan stack starting with " (to-s (peek stack)) " from column " (inc index))])))))
        (obscuring-king [{:keys [tableau] :as state}]
          (->> tableau
               (map-indexed
                (fn [index {[[rank] :as stack] :stack hidden :hidden}]
                  (if (and (= rank 13) (> hidden 0))
                    [stack (assoc-in state [:tableau index :stack] [])
                     (str "Moved " (-> stack peek to-s) "'s stack from column " (inc index))])))))
        (tableau-card [{:keys [tableau] :as state}]
          (->> tableau
               (map-indexed
                (fn [index {:keys [stack]}]
                  (if (seq stack)
                    [(peek stack) (update-in state [:tableau index :stack] pop)
                     (str "Moved " (-> stack peek to-s) " from tableau column " (inc index))])))))
        (foundation-card [{:keys [foundation] :as state}]
          (->> foundation
               (map-indexed
                (fn [index column]
                  (if (seq column)
                    [(peek column) (update-in state [:foundation index] pop)
                     (str "Moved " (-> column peek to-s) " from foundation column " (inc index))])))))
        (reveal-cards [query-cards]
          (fn [state]
            (->> (:tableau state)
                 (map-indexed
                  (fn [column-index {:keys [stack hidden] :as column}]
                    (if (and (empty? stack)
                             (> hidden 0))
                      (do
                        (get-history state)
                        (let [card (query-cards column-index hidden)]
                          (-> column
                              (update-in [:stack] conj card)
                              (update-in [:hidden] dec))))
                      column)))
                 vec
                 (assoc state :tableau))))
        (destinations [x y]
          (fn [& args]
            (-> (juxt x y) (apply args) flatten)))]
  (defn find-moves
    ([state]
       (let [moves (move-type
                    orphan orphan-parent
                    obscuring-king empty-tableau
                    tableau-card to-foundation
                    foundation-card to-tableau
                    waste-card (destinations to-foundation to-tableau))]
         (->> (moves state) (remove nil?))))
    ([state query-hidden]
       (->> state find-moves (map (reveal-cards query-hidden))))))

(defn query-hidden [col index]
  (.start (Thread. #(println "What is at column" (inc col) "card number" index "?")))
  (let [input (atom nil)]
    (while (not (valid-card? @input))
      (reset! input (->> clojure.edn/read repeatedly (take 2) card)))
    (println "Card read:" @input)
    @input))

(defn solve
  [initial-state]
  (let [get-next-moves (partial find-moves (memoize query-hidden))
        winning? (fn [state]
                   (if (every? #(= 13 (count %)) (state :foundation))
                     (get-history state)))]
    (loop [moves (->> initial-state normalize (conj clojure.lang.PersistentQueue/EMPTY))]
      (if-let [winning-moves (some winning? moves)]
        winning-moves
        (if (seq moves)
          (->> (peek moves)
               get-next-moves
               distinct
               (remove #(contains? moves %))
               (into (pop moves))
               recur))))))
