/* Copyright 2017 Stanford University, NVIDIA Corporation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "legion_context.h"
#include "legion_replication.h"

namespace Legion {
  namespace Internal {

    LEGION_EXTERN_LOGGER_DECLARATIONS

    const IndexSpace IndexSpaceReduction::identity = IndexSpace::NO_SPACE;
    const IndexPartitionID IndexPartitionReduction::identity = 0;
    const FieldSpace FieldSpaceReduction::identity = FieldSpace::NO_SPACE;
    const FieldID FieldReduction::identity = 0;
    const RegionTreeID LogicalRegionReduction::identity = 0;
#ifdef DEBUG_LEGION
    const ShardingID ShardingReduction::identity = UINT_MAX;
#endif

    /////////////////////////////////////////////////////////////
    // Repl Individual Task 
    /////////////////////////////////////////////////////////////

    //--------------------------------------------------------------------------
    ReplIndividualTask::ReplIndividualTask(Runtime *rt)
      : IndividualTask(rt)
    //--------------------------------------------------------------------------
    {
    }

    //--------------------------------------------------------------------------
    ReplIndividualTask::ReplIndividualTask(const ReplIndividualTask &rhs)
      : IndividualTask(rhs)
    //--------------------------------------------------------------------------
    {
      // should never be called
      assert(false);
    }

    //--------------------------------------------------------------------------
    ReplIndividualTask::~ReplIndividualTask(void)
    //--------------------------------------------------------------------------
    {
    }

    //--------------------------------------------------------------------------
    ReplIndividualTask& ReplIndividualTask::operator=(
                                                  const ReplIndividualTask &rhs)
    //--------------------------------------------------------------------------
    {
      // should never be called
      assert(false);
      return *this;
    }

    //--------------------------------------------------------------------------
    void ReplIndividualTask::activate(void)
    //--------------------------------------------------------------------------
    {
      activate_individual_task();
      sharding_functor = UINT_MAX;
    }

    //--------------------------------------------------------------------------
    void ReplIndividualTask::deactivate(void)
    //--------------------------------------------------------------------------
    {
#ifdef DEBUG_LEGION
      // Check to see if we picked the same shardingID as everyone else
      // In theory this has already triggered, but we might need to 
      // explicitly wait to get realm to admit that
      if (!replicate_mapped_barrier.has_triggered())
        replicate_mapped_barrier.wait();
      ShardingID actual;
#ifndef NDEBUG
      bool valid = 
#endif
        replicate_mapped_barrier.get_result(&actual, sizeof(actual));
      assert(valid);
      if (actual != sharding_functor)
      {
        if (mapper != NULL)
          mapper = runtime->find_mapper(current_proc, map_id);
        log_run.error("ERROR: Mapper %s chose different sharding functions %d "
                      "and %d for individual task %s (UID %lld) in %s "
                      "(UID %lld)", mapper->get_mapper_name(), sharding_functor,
                      actual, get_task_name(), get_unique_id(),
                      parent_ctx->get_task_name(), parent_ctx->get_unique_id());
        assert(false);
      }
#endif
      deactivate_individual_task();
      runtime->free_repl_individual_task(this);
    }

    //--------------------------------------------------------------------------
    void ReplIndividualTask::trigger_prepipeline_stage(void)
    //--------------------------------------------------------------------------
    {
#ifdef DEBUG_LEGION
      ReplicateContext *repl_ctx = dynamic_cast<ReplicateContext*>(parent_ctx);
      assert(repl_ctx != NULL);
#else
      ReplicateContext *repl_ctx = static_cast<ReplicateContext*>(parent_ctx);
#endif
      // Do the mapper call to get the sharding function to use
      if (mapper == NULL)
        mapper = runtime->find_mapper(current_proc, map_id); 
      Mapper::SelectShardingFunctorInput* input = repl_ctx->shard_manager;
      Mapper::SelectShardingFunctorOutput output;
      output.chosen_functor = UINT_MAX;
      mapper->invoke_task_select_sharding_functor(this, input, &output);
      if (output.chosen_functor == UINT_MAX)
      {
        log_run.error("Mapper %s failed to pick a valid sharding functor for "
                      "task %s (UID %lld)", mapper->get_mapper_name(),
                      get_task_name(), get_unique_id());
#ifdef DEBUG_LEGION
        assert(false);
#endif
        exit(ERROR_INVALID_MAPPER_OUTPUT);
      }
      this->sharding_functor = output.chosen_functor;
      // Now we can trigger our result barrier indicating when we are mapped
      // If we're in debug mode we also reduce our ShardingID so we can 
      // confirm that all the mappers picked the same one for this operation
#ifdef DEBUG_LEGION
      // Debug arrival so contribute the sharding ID
      Runtime::phase_barrier_arrive(replicate_mapped_barrier, 1/*count*/,
              get_mapped_event(), &sharding_functor, sizeof(sharding_functor));
#else
      // Normal arrival
      Runtime::phase_barrier_arrive(replicate_mapped_barrier, 1/*count*/,
                                    get_mapped_event());
#endif
      // Now we can do the normal prepipeline stage
      IndividualTask::trigger_prepipeline_stage();
    }

    //--------------------------------------------------------------------------
    void ReplIndividualTask::trigger_ready(void)
    //--------------------------------------------------------------------------
    {
#ifdef DEBUG_LEGION
      ReplicateContext *repl_ctx = dynamic_cast<ReplicateContext*>(parent_ctx);
      assert(repl_ctx != NULL);
#else
      ReplicateContext *repl_ctx = static_cast<ReplicateContext*>(parent_ctx);
#endif
      // Get the sharding function implementation to use from our context
      ShardingFunction *function = 
        repl_ctx->shard_manager->find_sharding_function(sharding_functor);
      // Figure out whether this shard owns this point
      ShardID owner_shard = function->find_owner(index_point, index_domain); 
      // If we own it we go on the queue, otherwise we complete early
      if (owner_shard != repl_ctx->owner_shard->shard_id)
      {
        // We don't own it, so we can pretend like we
        // mapped and executed this task already
        complete_mapping();
        complete_execution();
      }
      else // We own it, so it goes on the ready queue
        enqueue_ready_operation(); 
    }

    /////////////////////////////////////////////////////////////
    // Repl Index Task 
    /////////////////////////////////////////////////////////////

    //--------------------------------------------------------------------------
    ReplIndexTask::ReplIndexTask(Runtime *rt)
      : IndexTask(rt)
    //--------------------------------------------------------------------------
    {
    }

    //--------------------------------------------------------------------------
    ReplIndexTask::ReplIndexTask(const ReplIndexTask &rhs)
      : IndexTask(rhs)
    //--------------------------------------------------------------------------
    {
      // should never be called
      assert(false);
    }

    //--------------------------------------------------------------------------
    ReplIndexTask::~ReplIndexTask(void)
    //--------------------------------------------------------------------------
    {
    }

    //--------------------------------------------------------------------------
    ReplIndexTask& ReplIndexTask::operator=(const ReplIndexTask &rhs)
    //--------------------------------------------------------------------------
    {
      // should never be called
      assert(false);
      return *this;
    }

    //--------------------------------------------------------------------------
    void ReplIndexTask::activate(void)
    //--------------------------------------------------------------------------
    {
      activate_index_task();
      sharding_functor = UINT_MAX;
    }

    //--------------------------------------------------------------------------
    void ReplIndexTask::deactivate(void)
    //--------------------------------------------------------------------------
    {
#ifdef DEBUG_LEGION
      // Check to see if we picked the same shardingID as everyone else
      // In theory this has already triggered, but we might need to 
      // explicitly wait to get realm to admit that
      if (!replicate_mapped_barrier.has_triggered())
        replicate_mapped_barrier.wait();
      ShardingID actual;
#ifndef NDEBUG
      bool valid = 
#endif
        replicate_mapped_barrier.get_result(&actual, sizeof(actual));
      assert(valid);
      if (actual != sharding_functor)
      {
        if (mapper != NULL)
          mapper = runtime->find_mapper(current_proc, map_id);
        log_run.error("ERROR: Mapper %s chose different sharding functions %d "
                      "and %d for index task %s (UID %lld) in %s (UID %lld)", 
                      mapper->get_mapper_name(), sharding_functor, 
                      actual, get_task_name(), get_unique_id(),
                      parent_ctx->get_task_name(), parent_ctx->get_unique_id());
        assert(false);
      }
#endif 
      deactivate_index_task();
      runtime->free_repl_index_task(this);
    }

    //--------------------------------------------------------------------------
    void ReplIndexTask::trigger_prepipeline_stage(void)
    //--------------------------------------------------------------------------
    {
#ifdef DEBUG_LEGION
      ReplicateContext *repl_ctx = dynamic_cast<ReplicateContext*>(parent_ctx);
      assert(repl_ctx != NULL);
#else
      ReplicateContext *repl_ctx = static_cast<ReplicateContext*>(parent_ctx);
#endif
      // Do the mapper call to get the sharding function to use
      if (mapper == NULL)
        mapper = runtime->find_mapper(current_proc, map_id); 
      Mapper::SelectShardingFunctorInput* input = repl_ctx->shard_manager;
      Mapper::SelectShardingFunctorOutput output;
      output.chosen_functor = UINT_MAX;
      mapper->invoke_task_select_sharding_functor(this, input, &output);
      if (output.chosen_functor == UINT_MAX)
      {
        log_run.error("Mapper %s failed to pick a valid sharding functor for "
                      "task %s (UID %lld)", mapper->get_mapper_name(),
                      get_task_name(), get_unique_id());
#ifdef DEBUG_LEGION
        assert(false);
#endif
        exit(ERROR_INVALID_MAPPER_OUTPUT);
      }
      this->sharding_functor = output.chosen_functor;
      // Now we can do the normal prepipeline stage
      IndexTask::trigger_prepipeline_stage();
    }

    //--------------------------------------------------------------------------
    void ReplIndexTask::trigger_ready(void)
    //--------------------------------------------------------------------------
    {
#ifdef DEBUG_LEGION
      ReplicateContext *repl_ctx = dynamic_cast<ReplicateContext*>(parent_ctx);
      assert(repl_ctx != NULL);
#else
      ReplicateContext *repl_ctx = static_cast<ReplicateContext*>(parent_ctx);
#endif
      // Get the sharding function implementation to use from our context
      ShardingFunction *function = 
        repl_ctx->shard_manager->find_sharding_function(sharding_functor);
      // Compute the local index space of points for this shard
      const Domain &local_domain = 
        function->find_shard_domain(repl_ctx->owner_shard->shard_id, 
                                    index_domain);
      index_domain = local_domain;
      // If it's empty we're done, otherwise we go back on the queue
      if (local_domain.get_volume() == 0)
      {
        // We have no local points, so we can just trigger
        complete_mapping();
        complete_execution();
      }
      else // We have valid points, so it goes on the ready queue
        enqueue_ready_operation();
    }

    /////////////////////////////////////////////////////////////
    // Repl Index Fill Op 
    /////////////////////////////////////////////////////////////

    //--------------------------------------------------------------------------
    ReplIndexFillOp::ReplIndexFillOp(Runtime *rt)
      : IndexFillOp(rt)
    //--------------------------------------------------------------------------
    {
    }

    //--------------------------------------------------------------------------
    ReplIndexFillOp::ReplIndexFillOp(const ReplIndexFillOp &rhs)
      : IndexFillOp(rhs)
    //--------------------------------------------------------------------------
    {
      // should never be called
      assert(false);
    }

    //--------------------------------------------------------------------------
    ReplIndexFillOp::~ReplIndexFillOp(void)
    //--------------------------------------------------------------------------
    {
    }

    //--------------------------------------------------------------------------
    ReplIndexFillOp& ReplIndexFillOp::operator=(const ReplIndexFillOp &rhs)
    //--------------------------------------------------------------------------
    {
      // should never be called
      assert(false);
      return *this;
    }

    //--------------------------------------------------------------------------
    void ReplIndexFillOp::activate(void)
    //--------------------------------------------------------------------------
    {
      activate_index_fill();
      sharding_functor = UINT_MAX;
      mapper = NULL;
    }

    //--------------------------------------------------------------------------
    void ReplIndexFillOp::deactivate(void)
    //--------------------------------------------------------------------------
    {
#ifdef DEBUG_LEGION
      // Check to see if we picked the same shardingID as everyone else
      // In theory this has already triggered, but we might need to 
      // explicitly wait to get realm to admit that
      if (!replicate_mapped_barrier.has_triggered())
        replicate_mapped_barrier.wait();
      ShardingID actual;
#ifndef NDEBUG
      bool valid = 
#endif
        replicate_mapped_barrier.get_result(&actual, sizeof(actual));
      assert(valid);
      if (actual != sharding_functor)
      {
        if (mapper != NULL)
          mapper = runtime->find_mapper(
              parent_ctx->get_executing_processor(), map_id);
        log_run.error("ERROR: Mapper %s chose different sharding functions %d "
                      "and %d for index fill in task %s (UID %lld)", 
                      mapper->get_mapper_name(), sharding_functor, actual,
                      parent_ctx->get_task_name(), parent_ctx->get_unique_id());
        assert(false);
      }
#endif 
      deactivate_index_fill();
      runtime->free_repl_index_fill_op(this);
    }

    //--------------------------------------------------------------------------
    void ReplIndexFillOp::trigger_prepipeline_stage(void)
    //--------------------------------------------------------------------------
    {
#ifdef DEBUG_LEGION
      ReplicateContext *repl_ctx = dynamic_cast<ReplicateContext*>(parent_ctx);
      assert(repl_ctx != NULL);
#else
      ReplicateContext *repl_ctx = static_cast<ReplicateContext*>(parent_ctx);
#endif
      // Do the mapper call to get the sharding function to use
      if (mapper == NULL)
        mapper = runtime->find_mapper(
            parent_ctx->get_executing_processor(), map_id);
      Mapper::SelectShardingFunctorInput* input = repl_ctx->shard_manager;
      Mapper::SelectShardingFunctorOutput output;
      output.chosen_functor = UINT_MAX;
      mapper->invoke_fill_select_sharding_functor(this, input, &output);
      if (output.chosen_functor == UINT_MAX)
      {
        log_run.error("Mapper %s failed to pick a valid sharding functor for "
                      "index fill in task %s (UID %lld)", 
                      mapper->get_mapper_name(),
                      parent_ctx->get_task_name(), parent_ctx->get_unique_id());
#ifdef DEBUG_LEGION
        assert(false);
#endif
        exit(ERROR_INVALID_MAPPER_OUTPUT);
      }
      this->sharding_functor = output.chosen_functor;
      // Now we can do the normal prepipeline stage
      IndexFillOp::trigger_prepipeline_stage();
    }

    //--------------------------------------------------------------------------
    void ReplIndexFillOp::trigger_ready(void)
    //--------------------------------------------------------------------------
    {
#ifdef DEBUG_LEGION
      ReplicateContext *repl_ctx = dynamic_cast<ReplicateContext*>(parent_ctx);
      assert(repl_ctx != NULL);
#else
      ReplicateContext *repl_ctx = static_cast<ReplicateContext*>(parent_ctx);
#endif
      // Get the sharding function implementation to use from our context
      ShardingFunction *function = 
        repl_ctx->shard_manager->find_sharding_function(sharding_functor);
      // Compute the local index space of points for this shard
      const Domain &local_domain = 
        function->find_shard_domain(repl_ctx->owner_shard->shard_id, 
                                    index_domain);
      index_domain = local_domain;
      // If it's empty we're done, otherwise we go back on the queue
      if (local_domain.get_volume() == 0)
      {
        // We have no local points, so we can just trigger
        complete_mapping();
        complete_execution();
      }
      else // We have valid points, so it goes on the ready queue
        IndexFillOp::trigger_ready();
    }

    /////////////////////////////////////////////////////////////
    // Repl Copy Op 
    /////////////////////////////////////////////////////////////

    //--------------------------------------------------------------------------
    ReplCopyOp::ReplCopyOp(Runtime *rt)
      : CopyOp(rt)
    //--------------------------------------------------------------------------
    {
    }

    //--------------------------------------------------------------------------
    ReplCopyOp::ReplCopyOp(const ReplCopyOp &rhs)
      : CopyOp(rhs)
    //--------------------------------------------------------------------------
    {
      // should never be called
      assert(false);
    }

    //--------------------------------------------------------------------------
    ReplCopyOp::~ReplCopyOp(void)
    //--------------------------------------------------------------------------
    {
    }

    //--------------------------------------------------------------------------
    ReplCopyOp& ReplCopyOp::operator=(const ReplCopyOp &rhs)
    //--------------------------------------------------------------------------
    {
      // should never be called
      assert(false);
      return *this;
    }

    //--------------------------------------------------------------------------
    void ReplCopyOp::activate(void)
    //--------------------------------------------------------------------------
    {
      activate_copy();
      sharding_functor = UINT_MAX;
    }

    //--------------------------------------------------------------------------
    void ReplCopyOp::deactivate(void)
    //--------------------------------------------------------------------------
    {
#ifdef DEBUG_LEGION
      // Check to see if we picked the same shardingID as everyone else
      // In theory this has already triggered, but we might need to 
      // explicitly wait to get realm to admit that
      if (!replicate_mapped_barrier.has_triggered())
        replicate_mapped_barrier.wait();
      ShardingID actual;
#ifndef NDEBUG
      bool valid = 
#endif
        replicate_mapped_barrier.get_result(&actual, sizeof(actual));
      assert(valid);
      if (actual != sharding_functor)
      {
        if (mapper != NULL)
          mapper = runtime->find_mapper(
              parent_ctx->get_executing_processor(), map_id);
        log_run.error("ERROR: Mapper %s chose different sharding functions %d "
                      "and %d for copy in task %s (UID %lld)", 
                      mapper->get_mapper_name(), sharding_functor, actual,
                      parent_ctx->get_task_name(), parent_ctx->get_unique_id());
        assert(false);
      }
#endif
      deactivate_copy();
      runtime->free_repl_copy_op(this);
    }

    //--------------------------------------------------------------------------
    void ReplCopyOp::trigger_prepipeline_stage(void)
    //--------------------------------------------------------------------------
    {
#ifdef DEBUG_LEGION
      ReplicateContext *repl_ctx = dynamic_cast<ReplicateContext*>(parent_ctx);
      assert(repl_ctx != NULL);
#else
      ReplicateContext *repl_ctx = static_cast<ReplicateContext*>(parent_ctx);
#endif
      // Do the mapper call to get the sharding function to use
      if (mapper == NULL)
        mapper = runtime->find_mapper(
            parent_ctx->get_executing_processor(), map_id); 
      Mapper::SelectShardingFunctorInput* input = repl_ctx->shard_manager;
      Mapper::SelectShardingFunctorOutput output;
      output.chosen_functor = UINT_MAX; 
      mapper->invoke_copy_select_sharding_functor(this, input, &output);
      if (output.chosen_functor == UINT_MAX)
      {
        log_run.error("Mapper %s failed to pick a valid sharding functor for "
                      "copy in task %s (UID %lld)", mapper->get_mapper_name(),
                      parent_ctx->get_task_name(), parent_ctx->get_unique_id());
#ifdef DEBUG_LEGION
        assert(false);
#endif
        exit(ERROR_INVALID_MAPPER_OUTPUT);
      }
      this->sharding_functor = output.chosen_functor;
      // Now we can do the normal prepipeline stage
      CopyOp::trigger_prepipeline_stage();
    }

    //--------------------------------------------------------------------------
    void ReplCopyOp::trigger_ready(void)
    //--------------------------------------------------------------------------
    {
#ifdef DEBUG_LEGION
      ReplicateContext *repl_ctx = dynamic_cast<ReplicateContext*>(parent_ctx);
      assert(repl_ctx != NULL);
#else
      ReplicateContext *repl_ctx = static_cast<ReplicateContext*>(parent_ctx);
#endif
      // Get the sharding function implementation to use from our context
      ShardingFunction *function = 
        repl_ctx->shard_manager->find_sharding_function(sharding_functor);
      // Figure out whether this shard owns this point
      ShardID owner_shard = function->find_owner(index_point, index_domain); 
      // If we own it we go on the queue, otherwise we complete early
      if (owner_shard != repl_ctx->owner_shard->shard_id)
      {
        // We don't own it, so we can pretend like we
        // mapped and executed this copy already
        complete_mapping();
        complete_execution();
      }
      else // We own it, so do the base call
        CopyOp::trigger_ready();
    }

    /////////////////////////////////////////////////////////////
    // Repl Index Copy Op 
    /////////////////////////////////////////////////////////////

    //--------------------------------------------------------------------------
    ReplIndexCopyOp::ReplIndexCopyOp(Runtime *rt)
      : IndexCopyOp(rt)
    //--------------------------------------------------------------------------
    {
    }

    //--------------------------------------------------------------------------
    ReplIndexCopyOp::ReplIndexCopyOp(const ReplIndexCopyOp &rhs)
      : IndexCopyOp(rhs)
    //--------------------------------------------------------------------------
    {
      // should never be called
      assert(false);
    }

    //--------------------------------------------------------------------------
    ReplIndexCopyOp::~ReplIndexCopyOp(void)
    //--------------------------------------------------------------------------
    {
    }

    //--------------------------------------------------------------------------
    ReplIndexCopyOp& ReplIndexCopyOp::operator=(const ReplIndexCopyOp &rhs)
    //--------------------------------------------------------------------------
    {
      // should never be called
      assert(false);
      return *this;
    }

    //--------------------------------------------------------------------------
    void ReplIndexCopyOp::activate(void)
    //--------------------------------------------------------------------------
    {
      activate_index_copy();
      sharding_functor = UINT_MAX;
    }

    //--------------------------------------------------------------------------
    void ReplIndexCopyOp::deactivate(void)
    //--------------------------------------------------------------------------
    {
#ifdef DEBUG_LEGION
      // Check to see if we picked the same shardingID as everyone else
      // In theory this has already triggered, but we might need to 
      // explicitly wait to get realm to admit that
      if (!replicate_mapped_barrier.has_triggered())
        replicate_mapped_barrier.wait();
      ShardingID actual;
#ifndef NDEBUG
      bool valid = 
#endif
        replicate_mapped_barrier.get_result(&actual, sizeof(actual));
      assert(valid);
      if (actual != sharding_functor)
      {
        if (mapper != NULL)
          mapper = runtime->find_mapper(
              parent_ctx->get_executing_processor(), map_id);
        log_run.error("ERROR: Mapper %s chose different sharding functions %d "
                      "and %d for index copy in task %s (UID %lld)", 
                      mapper->get_mapper_name(), sharding_functor, actual,
                      parent_ctx->get_task_name(), parent_ctx->get_unique_id());
        assert(false);
      }
#endif
      deactivate_index_copy();
      runtime->free_repl_index_copy_op(this);
    }

    //--------------------------------------------------------------------------
    void ReplIndexCopyOp::trigger_prepipeline_stage(void)
    //--------------------------------------------------------------------------
    {
#ifdef DEBUG_LEGION
      ReplicateContext *repl_ctx = dynamic_cast<ReplicateContext*>(parent_ctx);
      assert(repl_ctx != NULL);
#else
      ReplicateContext *repl_ctx = static_cast<ReplicateContext*>(parent_ctx);
#endif
      // Do the mapper call to get the sharding function to use
      if (mapper == NULL)
        mapper = runtime->find_mapper(
            parent_ctx->get_executing_processor(), map_id); 
      Mapper::SelectShardingFunctorInput* input = repl_ctx->shard_manager;
      Mapper::SelectShardingFunctorOutput output;
      output.chosen_functor = UINT_MAX;
      mapper->invoke_copy_select_sharding_functor(this, input, &output);
      if (output.chosen_functor == UINT_MAX)
      {
        log_run.error("Mapper %s failed to pick a valid sharding functor for "
                      "index copy in task %s (UID %lld)", 
                      mapper->get_mapper_name(),
                      parent_ctx->get_task_name(), parent_ctx->get_unique_id());
#ifdef DEBUG_LEGION
        assert(false);
#endif
        exit(ERROR_INVALID_MAPPER_OUTPUT);
      }
      this->sharding_functor = output.chosen_functor;
      // Now we can do the normal prepipeline stage
      IndexCopyOp::trigger_prepipeline_stage();
    }

    //--------------------------------------------------------------------------
    void ReplIndexCopyOp::trigger_ready(void)
    //--------------------------------------------------------------------------
    {
#ifdef DEBUG_LEGION
      ReplicateContext *repl_ctx = dynamic_cast<ReplicateContext*>(parent_ctx);
      assert(repl_ctx != NULL);
#else
      ReplicateContext *repl_ctx = static_cast<ReplicateContext*>(parent_ctx);
#endif
      // Get the sharding function implementation to use from our context
      ShardingFunction *function = 
        repl_ctx->shard_manager->find_sharding_function(sharding_functor);
      // Compute the local index space of points for this shard
      const Domain &local_domain = 
        function->find_shard_domain(repl_ctx->owner_shard->shard_id, 
                                    index_domain);
      index_domain = local_domain;
      // If it's empty we're done, otherwise we go back on the queue
      if (local_domain.get_volume() == 0)
      {
        // We have no local points, so we can just trigger
        complete_mapping();
        complete_execution();
      }
      else // If we have any valid points do the base call
        IndexCopyOp::trigger_ready();
    }

    /////////////////////////////////////////////////////////////
    // Repl Deletion Op 
    /////////////////////////////////////////////////////////////

    //--------------------------------------------------------------------------
    ReplDeletionOp::ReplDeletionOp(Runtime *rt)
      : DeletionOp(rt)
    //--------------------------------------------------------------------------
    {
    }

    //--------------------------------------------------------------------------
    ReplDeletionOp::ReplDeletionOp(const ReplDeletionOp &rhs)
      : DeletionOp(rhs)
    //--------------------------------------------------------------------------
    {
      // should never be called
      assert(false);
    }

    //--------------------------------------------------------------------------
    ReplDeletionOp::~ReplDeletionOp(void)
    //--------------------------------------------------------------------------
    {
    }

    //--------------------------------------------------------------------------
    ReplDeletionOp& ReplDeletionOp::operator=(const ReplDeletionOp &rhs)
    //--------------------------------------------------------------------------
    {
      // should never be called
      assert(false);
      return *this;
    }

    //--------------------------------------------------------------------------
    void ReplDeletionOp::activate(void)
    //--------------------------------------------------------------------------
    {
      activate_deletion();
    }

    //--------------------------------------------------------------------------
    void ReplDeletionOp::deactivate(void)
    //--------------------------------------------------------------------------
    {
      deactivate_deletion();
      runtime->free_repl_deletion_op(this);
    }

    //--------------------------------------------------------------------------
    void ReplDeletionOp::trigger_ready(void)
    //--------------------------------------------------------------------------
    {
#ifdef DEBUG_LEGION
      ReplicateContext *repl_ctx = dynamic_cast<ReplicateContext*>(parent_ctx);
      assert(repl_ctx != NULL);
#else
      ReplicateContext *repl_ctx = static_cast<ReplicateContext*>(parent_ctx);
#endif
      // Shard 0 will hold all the deletions
      if (repl_ctx->owner_shard->shard_id == 0)
      {
        // We don't own it, so we can pretend like we
        // mapped and executed this deletion already 
        complete_mapping();
        complete_execution();
      }
      else // We own it, so enqueue it
        enqueue_ready_operation();
    }

    /////////////////////////////////////////////////////////////
    // Repl Pending Partition Op 
    /////////////////////////////////////////////////////////////

    //--------------------------------------------------------------------------
    ReplPendingPartitionOp::ReplPendingPartitionOp(Runtime *rt)
      : PendingPartitionOp(rt)
    //--------------------------------------------------------------------------
    {
    }

    //--------------------------------------------------------------------------
    ReplPendingPartitionOp::ReplPendingPartitionOp(
                                              const ReplPendingPartitionOp &rhs)
      : PendingPartitionOp(rhs)
    //--------------------------------------------------------------------------
    {
      // should never be called
      assert(false);
    }

    //--------------------------------------------------------------------------
    ReplPendingPartitionOp::~ReplPendingPartitionOp(void)
    //--------------------------------------------------------------------------
    {
    }

    //--------------------------------------------------------------------------
    ReplPendingPartitionOp& ReplPendingPartitionOp::operator=(
                                              const ReplPendingPartitionOp &rhs)
    //--------------------------------------------------------------------------
    {
      // should never be called
      assert(false);
      return *this;
    }

    /////////////////////////////////////////////////////////////
    // Repl Dependent Partition Op 
    /////////////////////////////////////////////////////////////

    //--------------------------------------------------------------------------
    ReplDependentPartitionOp::ReplDependentPartitionOp(Runtime *rt)
      : DependentPartitionOp(rt)
    //--------------------------------------------------------------------------
    {
    }

    //--------------------------------------------------------------------------
    ReplDependentPartitionOp::ReplDependentPartitionOp(
                                            const ReplDependentPartitionOp &rhs)
      : DependentPartitionOp(rhs)
    //--------------------------------------------------------------------------
    {
      // should never be called
      assert(false);
    }

    //--------------------------------------------------------------------------
    ReplDependentPartitionOp::~ReplDependentPartitionOp(void)
    //--------------------------------------------------------------------------
    {
    }

    //--------------------------------------------------------------------------
    ReplDependentPartitionOp& ReplDependentPartitionOp::operator=(
                                            const ReplDependentPartitionOp &rhs)
    //--------------------------------------------------------------------------
    {
      // should never be called
      assert(false);
      return *this;
    }

    /////////////////////////////////////////////////////////////
    // Repl Must Epoch Op 
    /////////////////////////////////////////////////////////////

    //--------------------------------------------------------------------------
    ReplMustEpochOp::ReplMustEpochOp(Runtime *rt)
      : MustEpochOp(rt)
    //--------------------------------------------------------------------------
    {
    }

    //--------------------------------------------------------------------------
    ReplMustEpochOp::ReplMustEpochOp(const ReplMustEpochOp &rhs)
      : MustEpochOp(rhs)
    //--------------------------------------------------------------------------
    {
      // should never be called
      assert(false);
    }

    //--------------------------------------------------------------------------
    ReplMustEpochOp::~ReplMustEpochOp(void)
    //--------------------------------------------------------------------------
    {
    }

    //--------------------------------------------------------------------------
    ReplMustEpochOp& ReplMustEpochOp::operator=(const ReplMustEpochOp &rhs)
    //--------------------------------------------------------------------------
    {
      // should never be called
      assert(false);
      return *this;
    }

    /////////////////////////////////////////////////////////////
    // Repl Timing Op 
    /////////////////////////////////////////////////////////////

    //--------------------------------------------------------------------------
    ReplTimingOp::ReplTimingOp(Runtime *rt)
      : TimingOp(rt)
    //--------------------------------------------------------------------------
    {
    }

    //--------------------------------------------------------------------------
    ReplTimingOp::ReplTimingOp(const ReplTimingOp &rhs)
      : TimingOp(rhs)
    //--------------------------------------------------------------------------
    {
      // should never be called
      assert(false);
    }

    //--------------------------------------------------------------------------
    ReplTimingOp::~ReplTimingOp(void)
    //--------------------------------------------------------------------------
    {
    }

    //--------------------------------------------------------------------------
    ReplTimingOp& ReplTimingOp::operator=(const ReplTimingOp &rhs)
    //--------------------------------------------------------------------------
    {
      // should never be called
      assert(false);
      return *this;
    }

    //--------------------------------------------------------------------------
    void ReplTimingOp::activate(void)
    //--------------------------------------------------------------------------
    {
      activate_timing();
    }

    //--------------------------------------------------------------------------
    void ReplTimingOp::deactivate(void)
    //--------------------------------------------------------------------------
    {
      deactivate_timing();
      runtime->free_repl_timing_op(this);
    }

    //--------------------------------------------------------------------------
    void ReplTimingOp::trigger_ready(void)
    //--------------------------------------------------------------------------
    {
#ifdef DEBUG_LEGION
      ReplicateContext *repl_ctx = dynamic_cast<ReplicateContext*>(parent_ctx);
      assert(repl_ctx != NULL);
#else
      ReplicateContext *repl_ctx = static_cast<ReplicateContext*>(parent_ctx);
#endif
      // Shard 0 will handle the timing operation
      if (repl_ctx->owner_shard->shard_id == 0)
      {
        // We don't own it, so we can pretend like we
        // mapped and executed this timing op already
        complete_mapping();
        complete_execution();
      }
      else // We own it, so do the normal thing
        Operation::trigger_ready();
    }

  }; // namespace Internal
}; // namespace Legion
