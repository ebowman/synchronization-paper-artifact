import scala.collection.mutable

// Define the Initiative case class
case class Initiative(name: String, workRequired: Int, value: Double = 1.0)

// Define the TeamMember case class
case class TeamMember(id: Int)

// Define TeamType sealed trait and its case objects
sealed trait TeamType
case object Foundation extends TeamType
case object Dependent extends TeamType

// Define the Team case class
case class Team(
                 name: String,
                 teamType: TeamType,
                 members: List[TeamMember],
                 initiatives: List[Initiative],
                 dependencies: List[Team] = List.empty, // Only for dependent teams
                 workOverrides: Map[String, Int] = Map.empty // Per-initiative work overrides (heterogeneous w_{i,j})
               ):
  /** Get the work required for an initiative on this team. */
  def workFor(init: Initiative): Int =
    workOverrides.getOrElse(init.name, init.workRequired)

// Define the Task case class
case class Task(
                 initiative: Initiative,
                 startTime: Int,
                 duration: Int,
                 assignedTeamMembers: List[TeamMember]
               )

// Define the TeamSchedule case class
case class TeamSchedule(
                         team: Team,
                         tasks: List[Task],
                         totalTime: Int
                       )

object WorkDivisionGenerator {

  // Function to generate all integer compositions of n into k positive integers
  def compositions(n: Int, k: Int): List[List[Int]] = {
    if (k == 1) {
      if (n >= 1) List(List(n))
      else Nil
    } else {
      (1 to n - k + 1).toList.flatMap { i =>
        compositions(n - i, k - 1).map(rest => i :: rest)
      }
    }
  }

  // Generate all permutations of a list
  def permutations[T](list: List[T]): List[List[T]] = list.permutations.toList

  // Cartesian product of a list of lists
  def cartesianProduct[T](lists: List[List[T]]): List[List[T]] = {
    lists.foldRight(List(List.empty[T])) { (currentList, acc) =>
      for {
        elem <- currentList
        combination <- acc
      } yield elem :: combination
    }
  }

  // Generate all possible work distributions for a team's initiatives
  // Uses team.workFor(initiative) for heterogeneous work support
  def generateWorkDistributions(
                                 team: Team,
                                 teamSize: Int
                               ): List[List[(Initiative, List[Int])]] = {
    val distributionsPerInitiative = team.initiatives.map { initiative =>
      val work = team.workFor(initiative)
      val compositionsList = compositions(work, teamSize)
      compositionsList.map(workList => (initiative, workList))
    }
    cartesianProduct(distributionsPerInitiative)
  }

  // Generate all possible schedules for a foundation team
  def generateFoundationTeamSchedules(team: Team): List[TeamSchedule] = {
    val teamMembers = team.members
    val teamSize = teamMembers.size
    val initiatives = team.initiatives

    val initiativePermutations = permutations(initiatives)

    val workDistributionsList = generateWorkDistributions(team, teamSize)

    val allSchedules = for {
      initiativeOrder <- initiativePermutations
      workDistributions <- workDistributionsList
      schedule <- buildTeamSchedule(team, initiativeOrder, workDistributions)
    } yield schedule

    allSchedules
  }

  // Build team schedule from initiative order and work distributions
  def buildTeamSchedule(
                         team: Team,
                         initiativeOrder: List[Initiative],
                         workDistributions: List[(Initiative, List[Int])]
                       ): Option[TeamSchedule] = {
    val teamMembers = team.members
    val teamSize = teamMembers.size

    val initiativeWorkMap = workDistributions.toMap

    // Build tasks for each team member
    val memberTasks = mutable.Map[TeamMember, List[Task]]()
    val currentTimePerMember = mutable.Map[TeamMember, Int]().withDefaultValue(0)

    for (initiative <- initiativeOrder) {
      val workAssignments = initiativeWorkMap(initiative)

      for (i <- 0 until teamSize) {
        val member = teamMembers(i)
        val work = workAssignments(i)
        val startTime = currentTimePerMember(member)
        val duration = work // Assuming 1 unit of work per time unit
        val task = Task(initiative, startTime, duration, List(member))
        memberTasks(member) = memberTasks.getOrElse(member, List()) :+ task
        currentTimePerMember(member) = startTime + duration
      }
    }

    // Total time is the maximum of currentTimePerMember
    val totalTime = currentTimePerMember.values.max

    val tasks = memberTasks.values.flatten.toList

    Some(TeamSchedule(team, tasks, totalTime))
  }

  // Compute initiative completion times from foundation team schedules
  def computeInitiativeCompletionTimes(foundationSchedules: List[TeamSchedule]): Map[Initiative, Int] = {
    val initiativeCompletionTimes = mutable.Map[Initiative, Int]().withDefaultValue(0)

    for (schedule <- foundationSchedules; task <- schedule.tasks) {
      val initiative = task.initiative
      val completionTime = task.startTime + task.duration
      initiativeCompletionTimes(initiative) = math.max(
        initiativeCompletionTimes.getOrElse(initiative, 0),
        completionTime
      )
    }

    initiativeCompletionTimes.toMap
  }

  // Generate all possible schedules for a dependent team, respecting dependencies
  def generateDependentTeamSchedules(
                                      team: Team,
                                      initiativeCompletionTimes: Map[Initiative, Int]
                                    ): List[TeamSchedule] = {
    val teamMembers = team.members
    val teamSize = teamMembers.size
    val initiatives = team.initiatives

    val initiativePermutations = permutations(initiatives)

    val workDistributionsList = generateWorkDistributions(team, teamSize)

    val allSchedules: Seq[TeamSchedule] = for {
      initiativeOrder <- initiativePermutations
      workDistributions <- workDistributionsList
      schedule <- buildDependentTeamSchedule(team, initiativeOrder, workDistributions, initiativeCompletionTimes)
    } yield schedule

    allSchedules.toList
  }

  // Build dependent team schedule, ensuring tasks start after dependencies are completed
  def buildDependentTeamSchedule(
                                  team: Team,
                                  initiativeOrder: List[Initiative],
                                  workDistributions: List[(Initiative, List[Int])],
                                  initiativeCompletionTimes: Map[Initiative, Int]
                                ): Option[TeamSchedule] = {
    val teamMembers = team.members
    val teamSize = teamMembers.size

    val initiativeWorkMap = workDistributions.toMap

    // Build tasks for each team member
    val memberTasks = mutable.Map[TeamMember, List[Task]]()
    val currentTimePerMember = mutable.Map[TeamMember, Int]().withDefaultValue(0)

    for (initiative <- initiativeOrder) {
      val workAssignments = initiativeWorkMap(initiative)
      val foundationCompletionTime = initiativeCompletionTimes.getOrElse(initiative, 0)

      for (i <- 0 until teamSize) {
        val member = teamMembers(i)
        val work = workAssignments(i)
        val startTime = math.max(currentTimePerMember(member), foundationCompletionTime)
        val duration = work // Assuming 1 unit of work per time unit
        val task = Task(initiative, startTime, duration, List(member))
        memberTasks(member) = memberTasks.getOrElse(member, List()) :+ task
        currentTimePerMember(member) = startTime + duration
      }
    }

    // Total time is the maximum of currentTimePerMember
    val totalTime = currentTimePerMember.values.max

    val tasks = memberTasks.values.flatten.toList

    Some(TeamSchedule(team, tasks, totalTime))
  }

  // Generate all possible schedules for all dependent teams
  def generateSchedulesForDependentTeams(
                                          dependentTeams: List[Team],
                                          initiativeCompletionTimes: Map[Initiative, Int]
                                        ): List[List[TeamSchedule]] = {
    val dependentSchedulesPerTeam = dependentTeams.map { team =>
      generateDependentTeamSchedules(team, initiativeCompletionTimes)
    }

    cartesianProduct(dependentSchedulesPerTeam)
  }

  // Generate all possible combined schedules
  def generateAllSchedules(
                            foundationTeams: List[Team],
                            dependentTeams: List[Team]
                          ): List[List[TeamSchedule]] = {
    // Generate all possible schedules for each foundation team
    val foundationTeamSchedulesList = foundationTeams.map(generateFoundationTeamSchedules)

    // Cartesian product of foundation team schedules
    val foundationSchedulesCombinations = cartesianProduct(foundationTeamSchedulesList)

    val allCombinedSchedules = for {
      foundationSchedules <- foundationSchedulesCombinations
      initiativeCompletionTimes = computeInitiativeCompletionTimes(foundationSchedules)
      dependentSchedulesList <- generateSchedulesForDependentTeams(dependentTeams, initiativeCompletionTimes)
    } yield foundationSchedules ++ dependentSchedulesList

    allCombinedSchedules
  }

}
