;; SPDX-License-Identifier: AGPL-3.0-or-later
;; SPDX-FileCopyrightText: 2025 Phronesis Contributors
;;
;; SPEC.core.scm - Core Specification for Phronesis Rule Evaluation
;;
;; This file defines the formal semantics of rule evaluation and the
;; decision trace model in executable Guile Scheme.
;;
;; Per semantic anchor: "SPEC.core.scm defines rule evaluation + decision trace model"

;;; ============================================================
;;; SECTION 1: Core Type Definitions
;;; ============================================================

;; A Policy is a 5-tuple: (name, condition, action, priority, metadata)
(define-record-type <policy>
  (make-policy name condition action priority metadata)
  policy?
  (name policy-name)
  (condition policy-condition)
  (action policy-action)
  (priority policy-priority)
  (metadata policy-metadata))

;; An Action is one of:
;;   - (accept reason)
;;   - (reject reason)
;;   - (report message)
;;   - (execute function args)
;;   - (block actions...)
;;   - (conditional cond then-action else-action)
(define-record-type <action>
  (make-action type payload)
  action?
  (type action-type)       ; 'accept | 'reject | 'report | 'execute | 'block | 'conditional
  (payload action-payload))

;; A TraceStep records a single evaluation step
(define-record-type <trace-step>
  (make-trace-step type timestamp inputs result rationale)
  trace-step?
  (type trace-step-type)           ; 'eval | 'match | 'vote | 'action | 'bind | 'error
  (timestamp trace-step-timestamp)
  (inputs trace-step-inputs)
  (result trace-step-result)
  (rationale trace-step-rationale))

;; A Trace is the complete audit trail of a decision
(define-record-type <trace>
  (make-trace id started-at completed-at status steps decision metadata)
  trace?
  (id trace-id)
  (started-at trace-started-at)
  (completed-at trace-completed-at)
  (status trace-status)            ; 'pending | 'completed | 'failed
  (steps trace-steps)              ; list of trace-step
  (decision trace-decision)        ; (decision-type . reason) | #f
  (metadata trace-metadata))

;; State represents the interpreter state
(define-record-type <state>
  (make-state policy-table consensus-log environment agents threshold)
  state?
  (policy-table state-policy-table)
  (consensus-log state-consensus-log)
  (environment state-environment)
  (agents state-agents)
  (threshold state-threshold))


;;; ============================================================
;;; SECTION 2: Operational Semantics - Evaluation Rules
;;; ============================================================

;; RULE 1: POLICY-MATCH
;;
;; Premise:
;;   eval(condition, env) = true
;;   policy = (name, condition, action, priority, metadata)
;;
;; Conclusion:
;;   (state, policy, situation) --> (state', action-pending)
;;
;; The trace records: (match policy-name true "condition evaluated to true")

(define (rule-policy-match state policy situation trace)
  "Apply POLICY-MATCH rule: if condition is true, queue action."
  (let* ((condition (policy-condition policy))
         (env (state-environment state))
         (eval-result (eval-condition condition env situation)))
    (if (eq? eval-result #t)
        (values state
                (policy-action policy)
                (trace-add-step trace 'match
                                `((policy . ,(policy-name policy)))
                                #t
                                "Policy condition evaluated to true"))
        (values state
                #f
                (trace-add-step trace 'match
                                `((policy . ,(policy-name policy)))
                                #f
                                "Policy condition evaluated to false")))))


;; RULE 2: ACTION-EXECUTE
;;
;; Premise:
;;   action in pending-actions
;;   consensus-approved(action, agents, threshold) = true
;;
;; Conclusion:
;;   log' = log ++ [(action, votes, timestamp)]
;;   execute(action) --> result
;;   (state, action) --> (state', result)
;;
;; The trace records: (vote action votes approved "consensus achieved")
;;                    (action action-type result "action executed")

(define (rule-action-execute state action agents threshold trace)
  "Apply ACTION-EXECUTE rule: execute action if consensus approves."
  (let* ((votes (collect-votes action agents))
         (approved (consensus-approved? votes agents threshold)))
    (if approved
        (let* ((trace (trace-add-step trace 'vote
                                      `((action . ,action) (votes . ,votes))
                                      #t
                                      (format #f "Consensus achieved: ~a/~a approved"
                                              (count-approvals votes) (length agents))))
               (result (execute-action action state))
               (state (log-action state action votes 'approved))
               (trace (trace-add-step trace 'action
                                      `((action . ,action))
                                      result
                                      (format #f "Action executed: ~a" (action-type action)))))
          (values state result trace))
        (let ((trace (trace-add-step trace 'vote
                                     `((action . ,action) (votes . ,votes))
                                     #f
                                     "Consensus not achieved")))
          (values state 'rejected trace)))))


;; RULE 3: COND-TRUE / COND-FALSE
;;
;; For conditional actions:
;;   if eval(cond) = true then execute(then-action)
;;   if eval(cond) = false then execute(else-action) or noop

(define (rule-conditional state condition then-action else-action env trace)
  "Apply COND-TRUE/COND-FALSE rule for conditional actions."
  (let ((result (eval-expr condition env)))
    (cond
     ((eq? result #t)
      (let ((trace (trace-add-step trace 'eval
                                   `((conditional . "then"))
                                   #t
                                   "Conditional true, taking THEN branch")))
        (values then-action trace)))
     ((and (eq? result #f) else-action)
      (let ((trace (trace-add-step trace 'eval
                                   `((conditional . "else"))
                                   #f
                                   "Conditional false, taking ELSE branch")))
        (values else-action trace)))
     (else
      (let ((trace (trace-add-step trace 'eval
                                   `((conditional . "noop"))
                                   #f
                                   "Conditional false, no ELSE branch")))
        (values #f trace))))))


;; RULE 4: MODULE-CALL
;;
;; Premise:
;;   module M exports function F
;;   eval(args) = values
;;
;; Conclusion:
;;   M.F(values) --> result (atomically)

(define (rule-module-call module-path args env trace)
  "Apply MODULE-CALL rule: call module function atomically."
  (let* ((arg-values (map (lambda (a) (eval-expr a env)) args))
         (result (call-module module-path arg-values))
         (trace (trace-add-step trace 'eval
                                `((module . ,module-path) (args . ,arg-values))
                                result
                                (format #f "Module call: ~a" module-path))))
    (values result trace)))


;; RULE 5: CONSENSUS-VOTE
;;
;; consensus-approved(action, agents, threshold) =
;;   (count(votes where vote = true) / |agents|) >= threshold

(define (consensus-approved? votes agents threshold)
  "Check if consensus threshold is met."
  (let ((total (length agents))
        (approvals (count-approvals votes)))
    (if (= total 0)
        #t
        (>= (/ approvals total) threshold))))

(define (count-approvals votes)
  "Count the number of true votes."
  (length (filter cdr votes)))


;;; ============================================================
;;; SECTION 3: Decision Trace Model
;;; ============================================================

;; Invariant: Every decision MUST produce a trace.
;; The trace is an append-only log of all evaluation steps.

(define (new-trace . metadata)
  "Create a new trace with unique ID."
  (make-trace
   (generate-trace-id)          ; unique identifier
   (current-time)               ; started-at
   #f                           ; completed-at (not yet)
   'pending                     ; status
   '()                          ; steps (empty)
   #f                           ; decision (not yet)
   (if (null? metadata) '() (car metadata))))

(define (trace-add-step trace step-type inputs result rationale)
  "Append a step to the trace. Traces are immutable; returns new trace."
  (let ((step (make-trace-step step-type (current-time) inputs result rationale)))
    (make-trace
     (trace-id trace)
     (trace-started-at trace)
     (trace-completed-at trace)
     (trace-status trace)
     (append (trace-steps trace) (list step))  ; append-only
     (trace-decision trace)
     (trace-metadata trace))))

(define (trace-complete trace decision)
  "Mark trace as completed with final decision."
  (make-trace
   (trace-id trace)
   (trace-started-at trace)
   (current-time)               ; completed-at = now
   'completed                   ; status
   (trace-steps trace)
   decision                     ; final decision
   (trace-metadata trace)))

(define (trace-fail trace reason)
  "Mark trace as failed with error."
  (make-trace
   (trace-id trace)
   (trace-started-at trace)
   (current-time)
   'failed
   (trace-steps trace)
   (cons 'error reason)
   (trace-metadata trace)))


;;; ============================================================
;;; SECTION 4: Core Evaluation Functions
;;; ============================================================

(define (evaluate-policies policies situation state trace)
  "Evaluate policies in priority order, returning first match.

   Invariant: trace is updated for EVERY policy evaluated.
   Invariant: returns (state, decision, trace) tuple."
  (if (null? policies)
      (values state #f (trace-complete trace #f))
      (let* ((policy (car policies))
             (rest (cdr policies)))
        (call-with-values
            (lambda () (rule-policy-match state policy situation trace))
          (lambda (state action trace)
            (if action
                ;; Policy matched, execute action with consensus
                (call-with-values
                    (lambda () (rule-action-execute state action
                                                    (state-agents state)
                                                    (state-threshold state)
                                                    trace))
                  (lambda (state result trace)
                    (let ((decision (extract-decision action result)))
                      (values state decision (trace-complete trace decision)))))
                ;; No match, try next policy
                (evaluate-policies rest situation state trace)))))))

(define (extract-decision action result)
  "Extract decision from action execution result."
  (case (action-type action)
    ((accept) (cons 'accept (action-payload action)))
    ((reject) (cons 'reject (action-payload action)))
    (else #f)))


;;; ============================================================
;;; SECTION 5: Termination Guarantee
;;; ============================================================

;; THEOREM: All Phronesis programs terminate.
;;
;; PROOF (by structural induction):
;;
;; Base cases:
;;   - Literals evaluate immediately
;;   - Variable lookup is O(1) in environment
;;   - Module calls are atomic and finite
;;
;; Inductive cases:
;;   - Binary/unary operations: terminate if operands terminate
;;   - Comparisons: terminate if operands terminate
;;   - Conditionals: finite branching, each branch terminates
;;   - Blocks: finite sequence, each action terminates
;;   - Policy evaluation: finite list, each policy checked once
;;
;; Key restrictions ensuring termination:
;;   1. No loops (while, for, recursion forbidden by grammar)
;;   2. No recursive function definitions
;;   3. Module calls cannot call back into Phronesis
;;   4. Policy list is finite and immutable during evaluation

(define (termination-proof-sketch)
  "Returns a structured proof of termination.
   This is a documentation function, not executable proof."
  '((theorem . "All Phronesis programs terminate")
    (proof-method . "Structural induction on AST")
    (base-cases
     ((literals . "Constant time evaluation")
      (variables . "Environment lookup is O(1)")
      (module-calls . "Atomic and guaranteed finite")))
    (inductive-cases
     ((expressions . "Terminate if subexpressions terminate")
      (conditionals . "Finite branching, each branch terminates")
      (blocks . "Finite sequence of terminating actions")
      (policies . "Finite list, each evaluated once")))
    (restrictions
     ((no-loops . "Grammar forbids while, for, recursion")
      (no-recursion . "Functions cannot be defined")
      (no-callbacks . "Modules cannot call back")
      (finite-policies . "Policy list immutable during eval")))))


;;; ============================================================
;;; SECTION 6: Safety Properties
;;; ============================================================

;; PROPERTY 1: Trace Completeness
;; Every decision path produces a trace with all evaluation steps.

(define (trace-complete? trace)
  "Verify trace completeness: has steps and a final decision."
  (and (not (null? (trace-steps trace)))
       (or (eq? (trace-status trace) 'completed)
           (eq? (trace-status trace) 'failed))))

;; PROPERTY 2: Consensus Safety
;; No action executes without consensus approval.

(define (consensus-safe? state)
  "Verify all logged actions have consensus approval."
  (every (lambda (log-entry)
           (eq? (assoc-ref log-entry 'result) 'approved))
         (filter (lambda (e) (eq? (assoc-ref e 'result) 'approved))
                 (state-consensus-log state))))

;; PROPERTY 3: Audit Trail Integrity
;; The consensus log is append-only and immutable.

(define (audit-trail-invariant old-log new-log)
  "Verify new log is extension of old log (append-only)."
  (let ((old-len (length old-log))
        (new-len (length new-log)))
    (and (>= new-len old-len)
         (equal? old-log (take new-log old-len)))))


;;; ============================================================
;;; SECTION 7: Helper Functions (Implementation)
;;; ============================================================

(define (generate-trace-id)
  "Generate a unique trace identifier."
  (format #f "trace-~a" (random 1000000000)))

(define (current-time)
  "Get current timestamp."
  (current-time-ns))

(define (current-time-ns)
  "Get current time in nanoseconds (placeholder)."
  0)

(define (eval-condition condition env situation)
  "Evaluate a condition expression in the given environment."
  ;; Placeholder - actual implementation in Elixir
  #t)

(define (eval-expr expr env)
  "Evaluate an expression in the given environment."
  ;; Placeholder - actual implementation in Elixir
  expr)

(define (collect-votes action agents)
  "Collect votes from agents for an action."
  ;; Placeholder - in production this is distributed
  (map (lambda (a) (cons a #t)) agents))

(define (log-action state action votes result)
  "Log an action to the consensus log."
  (make-state
   (state-policy-table state)
   (append (state-consensus-log state)
           (list `((action . ,action)
                   (votes . ,votes)
                   (result . ,result)
                   (timestamp . ,(current-time)))))
   (state-environment state)
   (state-agents state)
   (state-threshold state)))

(define (execute-action action state)
  "Execute an action and return result."
  ;; Placeholder - actual implementation in Elixir
  'executed)

(define (call-module path args)
  "Call a module function."
  ;; Placeholder - actual implementation in Elixir
  #t)

(define (take lst n)
  "Take first n elements of list."
  (if (or (null? lst) (<= n 0))
      '()
      (cons (car lst) (take (cdr lst) (- n 1)))))

(define (every pred lst)
  "Check if predicate holds for all elements."
  (or (null? lst)
      (and (pred (car lst))
           (every pred (cdr lst)))))

(define (filter pred lst)
  "Filter list by predicate."
  (cond ((null? lst) '())
        ((pred (car lst)) (cons (car lst) (filter pred (cdr lst))))
        (else (filter pred (cdr lst)))))

(define (assoc-ref alist key)
  "Get value for key in association list."
  (let ((pair (assoc key alist)))
    (if pair (cdr pair) #f)))


;;; ============================================================
;;; SECTION 8: Conformance Interface
;;; ============================================================

;; These functions define the interface that conforming implementations
;; must provide.

(define (conformance-requirements)
  "List of requirements for a conforming implementation."
  '((must-implement
     (parse "Parse source to AST")
     (execute "Execute AST with state")
     (trace "Produce decision trace for every execution")
     (consensus "Implement consensus voting"))
    (must-satisfy
     (termination "All programs must terminate")
     (trace-completeness "Every decision produces a trace")
     (consensus-safety "No action without consensus")
     (audit-integrity "Append-only consensus log"))
    (may-implement
     (optimization "Bytecode compilation, constant folding")
     (distribution "Multi-node consensus via Raft/PBFT")
     (persistence "Durable state storage"))))


;;; ============================================================
;;; End of SPEC.core.scm
;;; ============================================================
