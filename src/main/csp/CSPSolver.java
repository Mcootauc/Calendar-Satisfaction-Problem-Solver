package main.csp;

import java.time.LocalDate;
import java.util.*;

/**
 * CSP: Calendar Satisfaction Problem Solver
 * Provides a solution for scheduling some n meetings in a given
 * period of time and according to some unary and binary constraints
 * on the dates of each meeting.
 */
public class CSPSolver {

    // Backtracking CSP Solver
    // --------------------------------------------------------------------------------------------------------------
    
    /**
     * Public interface for the CSP solver in which the number of meetings,
     * range of allowable dates for each meeting, and constraints on meeting
     * times are specified.
     * @param nMeetings The number of meetings that must be scheduled, indexed from 0 to n-1
     * @param rangeStart The start date (inclusive) of the domains of each of the n meeting-variables
     * @param rangeEnd The end date (inclusive) of the domains of each of the n meeting-variables
     * @param constraints Date constraints on the meeting times (unary and binary for this assignment)
     * @return A list of dates that satisfies each of the constraints for each of the n meetings,
     *         indexed by the variable they satisfy, or null if no solution exists.
     */
    public static List<LocalDate> solve (int nMeetings, LocalDate rangeStart, LocalDate rangeEnd, Set<DateConstraint> constraints) {
    	List<LocalDate> assignments = new ArrayList<LocalDate>();
    	List<MeetingDomain> varDomains = new ArrayList<>();
    	for (int i = 0; i < nMeetings; i++) {
    		varDomains.add(new MeetingDomain(rangeStart, rangeEnd));
    	}
    	//updates var domains with the filtered domains
    	nodeConsistency(varDomains, constraints);
    	arcConsistency(varDomains, constraints);
        return(backTrack(nMeetings, assignments, varDomains, constraints, 0));
    }
    
    private static List<LocalDate> backTrack(int nMeetings, List<LocalDate> assignments, List<MeetingDomain> varDomains, Set<DateConstraint> constraints, int index) { 
    	if (assignments.size() == nMeetings) { return assignments; } 
    	for (MeetingDomain meetDom: varDomains) {
    		if (meetDom.domainValues.isEmpty()) { return null; }
    	}
    	//if at the end of domain size don't backtrack
    	//if (index == varDomains.size()) { return new ArrayList<>(varDomains.size()); }
    	MeetingDomain dates = varDomains.get(index);
    	for (LocalDate meetDate : dates.domainValues) {
    		assignments.add(meetDate);
    		if (checkConstraints(assignments, constraints)) { 
    			List<LocalDate> result = backTrack(nMeetings, assignments, varDomains, constraints, index + 1);
    			if (result != null) { return result; }
    		}
    		assignments.remove(assignments.size() - 1);
        }
    	return null;
    }
    
    private static boolean checkConstraints(List<LocalDate> assignments, Set<DateConstraint> constraints) {
		for (DateConstraint  constraint: constraints) {
			//checks if unary and has enough assignments to check constraints
			if(constraint.arity() == 1 && assignments.size() - 1 >= constraint.L_VAL) {
				if (!constraint.isSatisfiedBy(assignments.get(constraint.L_VAL), ((UnaryDateConstraint) constraint).R_VAL)) {
					return false;
				}
				
			}
			//if not unary then binary and checks if left and right val are able to be checked for constraints
			else if(constraint.arity() == 2 && assignments.size() - 1 >= constraint.L_VAL && assignments.size() - 1 >= ((BinaryDateConstraint) constraint).R_VAL) {
				if (!constraint.isSatisfiedBy(assignments.get(constraint.L_VAL), assignments.get(((BinaryDateConstraint) constraint).R_VAL))) {
					return false;
				}
				
			}
		}
		return true;
    }
    // Filtering Operations
    // --------------------------------------------------------------------------------------------------------------
    
    /**
     * Enforces node consistency for all variables' domains given in varDomains based on
     * the given constraints. Meetings' domains correspond to their index in the varDomains List.
     * @param varDomains List of MeetingDomains in which index i corresponds to D_i
     * @param constraints Set of DateConstraints specifying how the domains should be constrained.
     * [!] Note, these may be either unary or binary constraints, but this method should only process
     *     the *unary* constraints! 
     */
    public static void nodeConsistency (List<MeetingDomain> varDomains, Set<DateConstraint> constraints) {
    	for (DateConstraint constraint: constraints) {
    		//checks if binary
    		if(constraint.arity() == 2) { continue; }
    		MeetingDomain updateDom = varDomains.get(constraint.L_VAL);
    		Set<LocalDate> theDomVals = new HashSet<>(updateDom.domainValues);
    		for (LocalDate date: theDomVals) {
    			//gets rid of all the domains that aren't satisfied by the constraint
    			if (!constraint.isSatisfiedBy(date, ((UnaryDateConstraint) constraint).R_VAL)) {
    				updateDom.domainValues.remove(date);
    			}
    		}
    		//adds the domain into the list at the index of constraint's left val 
    		varDomains.set(constraint.L_VAL, updateDom);
    	}
    }
    
    /**
     * Enforces arc consistency for all variables' domains given in varDomains based on
     * the given constraints. Meetings' domains correspond to their index in the varDomains List.
     * @param varDomains List of MeetingDomains in which index i corresponds to D_i
     * @param constraints Set of DateConstraints specifying how the domains should be constrained.
     * [!] Note, these may be either unary or binary constraints, but this method should only process
     *     the *binary* constraints using the AC-3 algorithm! 
     */
    public static void arcConsistency (List<MeetingDomain> varDomains, Set<DateConstraint> constraints) {
    	Set<Arc> arcQ = new HashSet<Arc>();
    	Set<Arc> newArcs = new HashSet<Arc>();
    	for (DateConstraint constraint: constraints) {
    		if (constraint.arity() == 1) { continue; }
    		//adds all the binary constraints into the queue
    		arcQ.add(new Arc(constraint.L_VAL, ((BinaryDateConstraint) constraint).R_VAL, constraint));
    		Arc inverse = new Arc(((BinaryDateConstraint) constraint).R_VAL, constraint.L_VAL, ((BinaryDateConstraint) constraint).getReverse());
    		arcQ.add(inverse);
    	}
    	Set<Arc> possibleArcs = new HashSet<Arc>(arcQ);
    	while (!arcQ.isEmpty()) {
    		for (Arc qArc: arcQ) {
        		if (removeVals(varDomains, qArc)) {
        			for (Arc arc: possibleArcs) {
        				if (qArc.TAIL == arc.HEAD) {
        					Arc neighborArc = new Arc(arc.TAIL, arc.HEAD, arc.CONSTRAINT);
        					newArcs.add(neighborArc);
        				}
        			}
        		}
        	}
    		arcQ = new HashSet<>(newArcs);
    		newArcs.clear();
    	}
    }
    
    private static boolean removeVals (List<MeetingDomain> varDomains, Arc removedArc) {
    	boolean removed = false;
    	MeetingDomain domOfTail = varDomains.get(removedArc.TAIL);
    	Set<LocalDate> tailVals = new HashSet<>(domOfTail.domainValues), 
    			headVals = new HashSet<>(varDomains.get(removedArc.HEAD).domainValues);
    	for (LocalDate tailDate: tailVals) {
    		boolean containVal = false;
    		for(LocalDate headDate: headVals) {
    			if (removedArc.CONSTRAINT.isSatisfiedBy(tailDate, headDate)) { containVal = true; }
    		}
    		if(!containVal) { 
    			domOfTail.domainValues.remove(tailDate);
    			removed = true;
    		}
    	}
    	varDomains.set(removedArc.TAIL, domOfTail);
    	return removed;
    }
    
    /**
     * Private helper class organizing Arcs as defined by the AC-3 algorithm, useful for implementing the
     * arcConsistency method.
     * [!] You may modify this class however you'd like, its basis is just a suggestion that will indeed work.
     */
    private static class Arc {
        
        public final DateConstraint CONSTRAINT;
        public final int TAIL, HEAD;
        
        /**
         * Constructs a new Arc (tail -> head) where head and tail are the meeting indexes
         * corresponding with Meeting variables and their associated domains.
         * @param tail Meeting index of the tail
         * @param head Meeting index of the head
         * @param c Constraint represented by this Arc.
         * [!] WARNING: A DateConstraint's isSatisfiedBy method is parameterized as:
         * isSatisfiedBy (LocalDate leftDate, LocalDate rightDate), meaning L_VAL for the first
         * parameter and R_VAL for the second. Be careful with this when creating Arcs that reverse
         * direction. You may find the BinaryDateConstraint's getReverse method useful here.
         */
        public Arc (int tail, int head, DateConstraint c) {
            this.TAIL = tail;
            this.HEAD = head;
            this.CONSTRAINT = c;
        }
        
        @Override
        public boolean equals (Object other) {
            if (this == other) { return true; }
            if (this.getClass() != other.getClass()) { return false; }
            Arc otherArc = (Arc) other;
            return this.TAIL == otherArc.TAIL && this.HEAD == otherArc.HEAD && this.CONSTRAINT.equals(otherArc.CONSTRAINT);
        }
        
        @Override
        public int hashCode () {
            return Objects.hash(this.TAIL, this.HEAD, this.CONSTRAINT);
        }
        
        @Override
        public String toString () {
            return "(" + this.TAIL + " -> " + this.HEAD + ")";
        }
        
    }
    
}
