http://www.visualdataweb.de/webvowl/#iri=http://swat.cse.lehigh.edu/onto/univ-bench.owl


- (is type matter during verification? )
	forall s: src!X . exists t:trg!X . src!X.URI = trg!X.URI or
	forall s: src!EObject . exists t:trg!EObject . src!X.URI = trg!X.URI 
	
	- could X being relaxed during projection? e.g.
	
	rule gs2gs{
	from s1: src!GraduateStudent,
		s2: src!Course (s1.takesCourse = s2 and s2.type = GraduateCourse)
	to 
		t1:trg!GraduateStudent
		{
			URI <- s1.URI
			takesCourse <- s1.takesCourse
			isShow <- true
		},
		t2:trg!GraduateCourse
		{
			URI <- s2.URI
			isShow <- true
		}
	}
	
	or
	
	rule gs2gs{
	from s1: src!GraduateStudent,
		s2: src!Course (s1.takesCourse = s2)
	to 
		t1:trg!GraduateStudent
		{
			URI <- s1.URI
			takesCourse <- s1.takesCourse
			isShow <- true
		},
		t2:trg!Course
		{
			URI <- s2.URI
			isShow <- true
		}
	}