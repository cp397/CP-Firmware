//! \file comm_routing.c
//! \addtogroup Communications
//! @{

#include <stdbool.h>
#include "comm.h"
#include "serial.h"
#include "L2fram.h"



//TODO: consider the situation where too many nodes are added to the network (may only be noticed by an ancestor node)!

enum
{
    joinLen = 4, // Adding a node requires the parent ID and its own ID
    dropLen = 2  // Dropping a node only requires the node ID
};



//! \var uiNumEdges
//! \brief The number of edges in the edge list.  THis includes all descendants
static uint uiNumEdges = 0;
//! \struct S_nextEdge
//! \brief A structure pointer to indices in the edge list
static S_Edge *S_nextEdge;
//! \struct S_edgeList[MAX_EDGES]
//! \brief The edge list
static S_Edge S_edgeList[MAX_EDGES];
//! \var uiSelf
//! \brief Address of this node
static uint uiSelf;


/////////////////////////////////////////////////////////////////////////////////
//!
//! \brief Clears the edge list and sets the next edge pointers to the
//!              the edge list.
//!
//! \param uiAddress, the address of this node
//! \return 0
////////////////////////////////////////////////////////////////////////////////
uchar ucRoute_Init(uint uiAddress)
{
    //Save the address of this node
    uiSelf = uiAddress;

    //Clear values and edge list
    uiNumEdges = 0;
    for (uint i = 0; i < MAX_EDGES; i++)
    {
        S_edgeList[i].m_uiSrc = S_edgeList[i].m_uiDest = 0;
        S_edgeList[i].m_ucflags = F_NONE;
    }

    //Initialize non-zero values
    S_nextEdge = S_edgeList;

    return (0);
}

/////////////////////////////////////////////////////////////////////////////////
//!
//! \brief Adds addresses to the next available locations in the edge list
//!
//!
//! \param uiSrc, uiDest; source and destination node addresses
//! \return 0 for success, else error code
////////////////////////////////////////////////////////////////////////////////
static uchar ucAddEdge(uint uiSrc, uint uiDest)
{
    int i;
    S_Edge *S_ptr;
    if (uiNumEdges >= MAX_EDGES)
        return ROUTE_ERROR_TABLE_FULL;

    for (i = 0, S_ptr = S_edgeList; i < uiNumEdges; i++, S_ptr++)
    {
        // This edge already exists
        if (S_ptr->m_uiSrc == uiSrc && S_ptr->m_uiDest == uiDest)
        {
            if( ucL2FRAM_isHub() )
                S_nextEdge->m_ucflags = F_NONE;
            else
                S_nextEdge->m_ucflags = F_JOIN;

            return 0;
        }
    }

    //Save the edge nodes and increment the pointer.  Also add the edges to the update list.
    S_nextEdge->m_uiSrc   = uiSrc;
    S_nextEdge->m_uiDest  = uiDest;
    if( ucL2FRAM_isHub() )
        S_nextEdge->m_ucflags = F_NONE;
    else
        S_nextEdge->m_ucflags = F_JOIN;

    S_nextEdge++;                   // Increment edge list pointer
    uiNumEdges++;                   // Increment the total number of edges

    return (0);
}

/////////////////////////////////////////////////////////////////////////////////
//!
//! \brief Searches through the edge list and removes the specified edge
//!
//!
//! \param
//! \return
////////////////////////////////////////////////////////////////////////////////
uchar ucRoute_RemoveEdge(uint uiSrc, uint uiDest)
{
    int i, j, uiFoundEdge;
    S_Edge *S_ptr;

    //Fail if there are no edges to remove
    if (uiNumEdges == 0)
        return ROUTE_ERROR_TABLE_EMPTY;

    // Assume we will not find the edge
    uiFoundEdge = 0;

    //Find the edge
    for (i = 0, S_ptr = S_edgeList; i < uiNumEdges; i++, S_ptr++)
    {
        if (S_ptr->m_uiSrc == uiSrc && S_ptr->m_uiDest == uiDest)
        {
            //Remove the edge from the list and shift the proceeding edges over to fill in the gap
            S_ptr->m_uiSrc = S_ptr->m_uiDest = 0;
            uiFoundEdge = 1;
            for (j = i + 1; j < uiNumEdges; j++)
            {
                //Bounds check the index before shifting
                if(j > 0 && j < uiNumEdges)
                    S_edgeList[j - 1] = S_edgeList[j];
                else
                    return ROUTE_ERROR_INVALID_EDGE;
            }
            uiNumEdges--;
            S_nextEdge--;
            S_edgeList[uiNumEdges].m_uiSrc = 0;
            S_edgeList[uiNumEdges].m_uiDest = 0;
            S_edgeList[uiNumEdges].m_ucflags = F_NONE;
        }
    }

    //Fail if the specified edge wasn't found in the graph
    if (uiFoundEdge == 0)
        return ROUTE_ERROR_DOES_NOT_EXIST;

    return (0);
}

/////////////////////////////////////////////////////////////////////////////////
//!
//! \brief Gets the next destination address for a node that may be several hops away
//!
//! In the event that the destination address is a child of self then the function returns
//! the self address.
//!
//! \param uiDest
//! \return uiSrc
////////////////////////////////////////////////////////////////////////////////
uint uiRoute_GetNextHop(uint uiDest)
{
    int i, j;
    S_Edge *S_ptr, *S_ptr2;
    uint uiSrc;

    //Search for edge with the matching destination (if it exists)
    for (i = 0, S_ptr = S_edgeList; i < uiNumEdges; i++, S_ptr++)
    {
        if (S_ptr->m_uiDest == uiDest)
        {
            // If the child is a direct child of this node then return the destination address
            if(S_ptr->m_uiSrc == uiSelf)
            {
                if(S_ptr->m_ucflags & F_DROP)
                    return 0;
                else
                    return uiDest;
            }

            //If the src is not the self then save the parent (source) of the edge
            uiSrc = S_ptr->m_uiSrc;
            break;
        }
    }

    //Fail if there isn't an edge with a matching destination
    if (i == uiNumEdges)
        return 0; //Error - 0 is an invalid address

//TODO: add in some logic to prevent infinite loops (circular graph connections) in the while loop below

    //Backtrack the src node address to one of the child nodes of this address
    while (1)
    {
        //Look through each edge
        for (j = 0, S_ptr2 = S_edgeList; j < uiNumEdges; j++, S_ptr2++)
        {
            //If the current edge leads to src then src is a child of this node (and therefore it is the next hop)
            if (    S_ptr2->m_uiDest == uiSrc
                 && S_ptr2->m_uiSrc  == uiSelf)
            {
                if(S_ptr->m_ucflags & F_DROP)
                    return 0;
                else
                    return uiSrc;
            }
            //Otherwise continue backtracking from src
            else if (S_ptr2->m_uiDest == uiSrc)
            {
                uiSrc = S_ptr2->m_uiSrc;
                break;
            }
        }

        //If the backtracking failed then return fail
        if (j == uiNumEdges)
            break;
    }

    //Fail because the next hop wasn't found
    return 0; //Error - 0 is an invalid address
}

/////////////////////////////////////////////////////////////////////////////////
//!
//! \brief Adds a node to the list along with its edge list
//!
//!
//! \param
//! \return
////////////////////////////////////////////////////////////////////////////////
uchar ucRoute_NodeJoin(uint uiParent, uint uiChild, S_Edge* S_edges, int iNumEdges)
{
    int i;
    uchar ucReturnValue;
    S_Edge *S_ptr;

    //Add all of the edges in the subtree of this node
    for (i = 0, S_ptr = S_edges; i < iNumEdges; i++, S_ptr++)
    {
        ucReturnValue = ucAddEdge(S_ptr->m_uiSrc, S_ptr->m_uiDest);
        if (ucReturnValue != 0)
            return ucReturnValue;
    }

    //Add the new edge from the 'mount point' node to the new node
    if(uiParent == 0) return ucAddEdge(uiSelf, uiChild);      //The node is joining as a direct child
    else return ucAddEdge(uiParent, uiChild);               //The node is joining as a non-child descendant
}


/////////////////////////////////////////////////////////////////////////////////
//!
//! \brief Flags nodes in the edge list to be dropped, the nodes will be removed
//! once the parent node has been notified, or when the connection to the parent
//! is dropped
//!
//! \param uiChild
//! \return 0
////////////////////////////////////////////////////////////////////////////////
uchar ucRoute_NodeUnjoin(uint uiChild)
{
    int i;
    S_Edge *S_ptr;
    uint uiTmp;

    //Allocate a remove stack on the system stack
    uint removeStack[MAX_NODES];
    int iStackSize = 0;

    //Fail if there are no edges to remove
    if (uiNumEdges == 0)
        return ROUTE_ERROR_TABLE_EMPTY;

    //Find the node that is being unjoined and then:
    //   1 - remove the edge that connects the unjoining node
    //   2 - add the node to the remove stack so that its descendants will also be removed below
    for (i = 0, S_ptr = S_edgeList; i < uiNumEdges; i++, S_ptr++)
    {
        // NOTE: Loop through the entire list to ensure every instance of uiChild will be removed.
        //       There should only be one instance of a node a a direct descendant of the parent, but hey
        //       doesn't hurt to be extra thorough.

        //Flag the unjoining node for a drop
        if (S_ptr->m_uiDest == uiChild)
        {
            S_ptr->m_ucflags = F_DROP | F_ROOT;

            // Set the pending flag so that the update will be cleared e
            if( ucL2FRAM_isHub() )
                S_ptr->m_ucflags |= F_PENDING;

            // Add one copy of the unjoining node to the remove stack
            if( iStackSize == 0 )
                removeStack[iStackSize++] = uiChild;
        }
    }

    //While there are nodes to remove from the edge list...
    while (iStackSize > 0)
    {
        //Pop the next node to be removed off of the remove stack
        uiTmp = removeStack[--iStackSize];

        //Look through the edge list for the all edges originating at node that is being removed
        for (i = 0, S_ptr = S_edgeList; i < uiNumEdges; i++, S_ptr++)
        {
            //If this edge originates at the node being removed then...
            if (S_ptr->m_uiSrc == uiTmp)
            {
                //Push the destination node of the edge to the remove stack so it will also be removed
                removeStack[iStackSize++] = S_ptr->m_uiDest;

                S_ptr->m_ucflags = (F_PENDING | F_DROP);
            }
        }
    }

    // The root node is all that is required to inform parent nodes that the state of the network
    // has changed.  We can remove all child nodes immediately.
    vRoute_clearPendingUpdates(true);

    return (0);
}

/////////////////////////////////////////////////////////////////////////////////
//!
//! \brief Returns either the number of added or dropped
//!
//! \param ucIndex
//! \return ucCount, the number of update records
////////////////////////////////////////////////////////////////////////////////
uchar ucRoute_GetUpdateCount(uchar ucAddOrDrop)
{
    uchar ucCount = 0;
    S_Edge *S_ptr = S_edgeList;

    for (uchar ucIndex = 0; ucIndex < uiNumEdges; ucIndex++, S_ptr++)
        if (S_ptr->m_ucflags & ucAddOrDrop)
            ucCount++;

    return ucCount;
}

/////////////////////////////////////////////////////////////////////////////////
//!
//! \brief Returns either the number of bytes for added or dropped nodes
//!
//! \param ucIndex
//! \return S_edgeList[ucIndex].m_uiSrc
////////////////////////////////////////////////////////////////////////////////
uchar ucRoute_GetUpdateCountBytes(uchar ucAddOrDrop)
{
    uchar ucJoinVal;
    uchar ucDropVal;
    uchar ucRetVal;

    ucRetVal = 0;

    if (ucAddOrDrop & F_JOIN)
    {
        ucJoinVal = ucRoute_GetUpdateCount(F_JOIN);
        ucJoinVal *= joinLen;
        ucRetVal += ucJoinVal;
    }
    if (ucAddOrDrop & F_DROP)
    {
        ucDropVal = ucRoute_GetUpdateCount(F_DROP);
        ucDropVal *= dropLen;
        ucRetVal += ucDropVal;
    }

    return ucRetVal;
}


bool contains(uint *p, uint id, uchar len)
{
    uchar i;
    for( i = 0; i < len; ++i )
    {
        if( p[i] == id )
            return true;
    }
    return false;
}


/////////////////////////////////////////////////////////////////////////////////
//!
//! \brief Loads the update table into a buffer, typically the message buffer.
//!
//! This function first loads the joins then the drops.  The joins and drops are
//! preceded by a byte indicating the length of the join or drop section.
//!
//!
//! \param *ucaBuff, the message buffer; ucSpaceAvail, space in bytes,
//! \return none
////////////////////////////////////////////////////////////////////////////////
void vRoute_GetUpdates(volatile uchar *ucaBuff, uchar ucSpaceAvail)
{
    uchar ucJoinBytes;
    uchar ucDropBytes = 0;
    S_Edge *S_ptr = S_edgeList;

    uint mySn = uiL2FRAM_getSnumLo16AsUint();

    // Get drop update length
    ucDropBytes = ucRoute_GetUpdateCountBytes(F_DROP);

    // Only append drops if there are any and if there is enough room for the length and one address
    if (ucDropBytes != 0 && ucSpaceAvail >= dropLen)
    {
        // Fill drop count field
        if (ucDropBytes < ucSpaceAvail)
            *ucaBuff++ = ucDropBytes;
        else
            *ucaBuff++ = ucSpaceAvail;

        S_ptr = S_edgeList;
        // Fill drop node addresses
        for (uint i = 0; i < uiNumEdges & ucSpaceAvail >= dropLen; ++i, S_ptr++)
        {
            if( (S_ptr->m_ucflags & (F_ROOT | F_DROP)) )
            {
                if( S_ptr->m_uiSrc == mySn  )
                {
                    // Add the addresses to the message
                    *ucaBuff++ = (uchar) (S_ptr->m_uiDest >> 8);
                    *ucaBuff++ = (uchar) S_ptr->m_uiDest;
                    ucSpaceAvail -= dropLen;
                }
                else
                {
                    // Add the addresses to the message
                    *ucaBuff++ = (uchar) (S_ptr->m_uiSrc >> 8);
                    *ucaBuff++ = (uchar) S_ptr->m_uiSrc;
                    ucSpaceAvail -= dropLen;
                }
            }
            S_ptr->m_ucflags |= F_PENDING;
        }
    }
    else
    {
        *ucaBuff++ = 0;
    }

    // Get join count
    ucJoinBytes = ucRoute_GetUpdateCountBytes(F_JOIN);

    // If there are no joins then don't bother iterating through the list
    if (ucJoinBytes != 0 && ucSpaceAvail >= joinLen)
    {
        // Fill join count field
        if (ucJoinBytes < ucSpaceAvail)
            *ucaBuff++ = ucJoinBytes;
        else
            *ucaBuff++ = ucSpaceAvail;

        S_ptr = S_edgeList;
        // Fill join node addresses
        for (uint i = 0; i < uiNumEdges & ucSpaceAvail >= joinLen; ++i, S_ptr++)
        {
            if (S_ptr->m_ucflags & F_JOIN)
            {
                // Add the addresses to the message
                *ucaBuff++ = (uchar) (S_ptr->m_uiSrc >> 8);
                *ucaBuff++ = (uchar) S_ptr->m_uiSrc;
                *ucaBuff++ = (uchar) (S_ptr->m_uiDest >> 8);
                *ucaBuff++ = (uchar) S_ptr->m_uiDest;
                S_ptr->m_ucflags |= F_PENDING;
                ucSpaceAvail -= joinLen;
            }
        }
    }
    else
    {
        *ucaBuff++ = 0;
    }

}//END: vRoute_GetUpdates();


/////////////////////////////////////////////////////////////////////////////////
//!
//! \brief Handle updates to edgelist after updating parent
//! If called, it means that the child attempted to push the updates to a parent
//! If it failed, set the list of updates back to the previous status' so the node
//! can retry next time around otherwise clear the join or drop flag
//!
//! \param success
//////////////////////////////////////////////////////////////////////////////////
void vRoute_clearPendingUpdates(bool success)
{
    // IMPORTANT: Only increment edge pointer and index when not removing an edge because
    //            the ucRemoveEdge function decrements edge count and shifts the list

    S_Edge* S_ptr = S_edgeList;

    for (uint i = 0; i < uiNumEdges; )
    {
        // If not pending then move to the next edge
        if (S_ptr->m_ucflags & F_PENDING)
        {
            S_ptr->m_ucflags &= ~F_PENDING;

            // If the push wasn't successful then don't clear F_DROP or F_JOIN
            if (success && (S_ptr->m_ucflags & F_DROP))
            {
                ucRoute_RemoveEdge(S_ptr->m_uiSrc, S_ptr->m_uiDest);
            }
            else if (success && (S_ptr->m_ucflags & F_JOIN))
            {
                S_ptr->m_ucflags = F_NONE;
                S_ptr++;
                i++;
            }
            else
            {
                S_ptr++;
                i++;
            }
        }
        else
        {
            S_ptr++;
            i++;
        }
    }
}


/////////////////////////////////////////////////////////////////////////////////
//!
//! \brief Adds updates to the edge list.
//!
//!
//! \param *ucaBuff, the message buffer
//! \return none
////////////////////////////////////////////////////////////////////////////////
void vRoute_SetUpdates(volatile uchar *ucaBuff)
{
    S_Edge S_EdgeLocal[MAX_UPDATES];
    uchar ucJoins;
    uchar ucDrops;
    uint uiDropAddr;
    uchar ucCount;

    // Get the number of drops in terms of nodes instead of bytes
    ucDrops = (*ucaBuff++)/2;

    for(ucCount = 0; ucCount < ucDrops; ucCount++)
    {
        uiDropAddr = (uint) (*ucaBuff++);
        uiDropAddr = uiDropAddr << 8;
        uiDropAddr |= (uint) (*ucaBuff++);

        ucRoute_NodeUnjoin(uiDropAddr);
    }

    // Convert the join field from length for the following loop
    ucJoins = (*ucaBuff++)/4;

    for(ucCount = 0; ucCount < ucJoins; ucCount++)
    {
        S_EdgeLocal[ucCount].m_uiSrc = (uint) (*ucaBuff++<<8);
        S_EdgeLocal[ucCount].m_uiSrc |= (uint) (*ucaBuff++);
        S_EdgeLocal[ucCount].m_uiDest = (uint) (*ucaBuff++<<8);
        S_EdgeLocal[ucCount].m_uiDest |= (uint) (*ucaBuff++);

        ucAddEdge(S_EdgeLocal[ucCount].m_uiSrc, S_EdgeLocal[ucCount].m_uiDest);
    }
}

void vRoute_DisplayEdges(void)
{
    uint uiEdgeCount;

    vSERIAL_sout("SOURCE    DESTINATION   STATUS", 30);
    vSERIAL_crlf();
    for(uiEdgeCount = 0; uiEdgeCount < uiNumEdges; uiEdgeCount++)
    {
        vSERIAL_HB16out(S_edgeList[uiEdgeCount].m_uiSrc);
        vSERIAL_sout("      ", 6);
        vSERIAL_HB16out(S_edgeList[uiEdgeCount].m_uiDest);
        vSERIAL_sout("          ", 10);
        if( S_edgeList[uiEdgeCount].m_ucflags == F_NONE)
            vSERIAL_sout("active ", 7);
        if( S_edgeList[uiEdgeCount].m_ucflags & F_ROOT)
            vSERIAL_sout("root   ", 7);
        if( S_edgeList[uiEdgeCount].m_ucflags & F_JOIN)
            vSERIAL_sout("joined ", 7);
        if( S_edgeList[uiEdgeCount].m_ucflags & F_DROP)
            vSERIAL_sout("droppd ", 7);
        if( S_edgeList[uiEdgeCount].m_ucflags & F_PENDING)
            vSERIAL_sout("pendng ", 7);

        vSERIAL_crlf();
    }

}

///////////////////////////////////////////////////////////////////////////////
//!
//! \brief Returns the number of edges
//!
//! \param none
//! \return uiNumEdges
///////////////////////////////////////////////////////////////////////////////
uint uiRoute_getNumEdges(void)
{
    return uiNumEdges;
}

//! @}
